module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.Category
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Length.IndexAdditivity
public import StacksFrontier.RingTheory.Length.IndexComparison
public import StacksFrontier.RingTheory.Length.MaximalIdealPower
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive

/-!
# The Euler characteristic of a coherent triple: a common coherent refinement

The functors to the closed fibre and the auxiliary lemmas on kernels, biproducts and
restrictions used throughout the proof of **Stacks Tag 0F25**, and the construction of a
coherent module mapping to two prepared extensions of the same coherent triple and agreeing
with both over the punctured spectrum and over the closed fibre
(`exists_compatible_coherent_refinement`).

This file is part of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic`; see there
for the overview and references.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

-- The complete-lattice structure on `F.Submodule` already exists upstream; it is made available
-- locally rather than re-declared, because an anonymous `local instance` with this type gets a
-- derived name that collides with the identical one in
-- `StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic`.
attribute [local instance] SheafOfModules.Submodule.instCompleteLattice

/-- Restriction of scalars along `A → A / fA`, with the quotient map spelled as a morphism of
`CommRingCat`. That is the spelling in which the extension of scalars appearing in
`AlgebraicGeometry.specPullbackSectionsIso` lands, so writing the restriction this way puts
the two functors between literally the same categories. -/
noncomputable def restrictScalarsQuot (A : Type u) [CommRing A] (f : A) :
    ModuleCat (CommRingCat.of (A ⧸ Ideal.span {f})) ⥤ ModuleCat A :=
  ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))).hom

noncomputable abbrev closedFibreSectionsFunctor
    (A : Type u) [CommRing A] (f : A) :
    (baseScheme A).Modules ⥤ ModuleCat A :=
  Scheme.Modules.pullback (closedImmersion A f) ⋙
    moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f})) ⋙ restrictScalarsQuot A f

noncomputable def closedFibreGammaFunctor
    (A : Type u) [CommRing A] (f : A) :
    (closedFibre A f).Modules ⥤ ModuleCat A :=
  moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f})) ⋙ restrictScalarsQuot A f

noncomputable def closedFibreAdjunctionMap
    (A : Type u) [CommRing A] (f : A)
    {G : (baseScheme A).Modules} {H : (closedFibre A f).Modules}
    (α : (Scheme.Modules.pullback (closedImmersion A f)).obj G ⟶ H) :
    G ⟶ (Scheme.Modules.pushforward (closedImmersion A f)).obj H :=
  (Scheme.Modules.pullbackPushforwardAdjunction (closedImmersion A f)).homEquiv G H α

lemma closedFibreAdjunctionMap_comp
    (A : Type u) [CommRing A] (f : A)
    {G G' : (baseScheme A).Modules} {H : (closedFibre A f).Modules}
    (g : G' ⟶ G)
    (α : (Scheme.Modules.pullback (closedImmersion A f)).obj G ⟶ H) :
    closedFibreAdjunctionMap A f ((Scheme.Modules.pullback (closedImmersion A f)).map g ≫ α) =
      g ≫ closedFibreAdjunctionMap A f α :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (closedImmersion A f)).homEquiv_naturality_left g α

lemma isCoherent_biprod {X : Scheme.{u}} (F G : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) : (F ⊞ G).IsCoherent :=
  (_root_.SheafOfModules.isCoherent_iff _).mpr
    (Stacks.SheafOfModules.isCoherent_X₂_of_shortExact
      (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact
      ((_root_.SheafOfModules.isCoherent_iff F).mp hF)
      ((_root_.SheafOfModules.isCoherent_iff G).mp hG))

lemma isIso_restrict_kernel_ι_of_map_eq_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {F G : Y.Modules} (φ : F ⟶ G)
    (hφ : (Scheme.Modules.restrictFunctor f).map φ = 0) :
    IsIso ((Scheme.Modules.restrictFunctor f).map (kernel.ι φ)) := by
  let R := Scheme.Modules.restrictFunctor f
  have : IsIso (kernel.ι (R.map φ)) := kernel.ι_of_zero hφ
  rw [← kernelComparison_comp_ι]
  infer_instance

lemma isIso_restrict_adjunctionMap_of_iso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (F : Y.Modules) (G : X.Modules)
    (e : F.restrict f ≅ G) :
    IsIso ((Scheme.Modules.restrictFunctor f).map
      ((Scheme.Modules.restrictAdjunction f).homEquiv F G e.hom)) := by
  let adj := Scheme.Modules.restrictAdjunction f
  let L := Scheme.Modules.restrictFunctor f
  have hunit : IsIso (L.map (adj.unit.app F)) := by
    have : IsIso (L.map (adj.unit.app F) ≫ adj.counit.app (L.obj F)) := by
      rw [adj.left_triangle_components F]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp this
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  infer_instance

private lemma app_eq_zero_of_restrict_eq_zero {X : Scheme.{u}}
    (U : X.Opens) {F G : X.Modules} (φ : F ⟶ G)
    (hφ : (Scheme.Modules.restrictFunctor U.ι).map φ = 0)
    (V : X.Opens) (hV : V ≤ U) : φ.app V = 0 := by
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have himage : U.ι ''ᵁ W = V := by
    ext point
    simp [W, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have heq := congrArg (fun ψ => ψ.app W) hφ
  change φ.app (U.ι ''ᵁ W) = 0 at heq
  rwa [himage] at heq

private lemma restrict_pushforward_eq_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) {F G : X.Modules} (φ : F ⟶ G)
    (hφ : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map φ = 0) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map φ) = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  change φ.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) = 0
  exact app_eq_zero_of_restrict_eq_zero (f ⁻¹ᵁ U) φ hφ _
    (Scheme.Hom.preimage_mono f (U.ι_image_le V))

lemma restrict_closedFibreAdjunctionMap_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    {G : (baseScheme A).Modules} {H : (closedFibre A f).Modules}
    (δ : (Scheme.Modules.pullback (closedImmersion A f)).obj G ⟶ H)
    (hδ : (Scheme.Modules.restrictFunctor (puncturedClosedFibre A f).ι).map δ = 0) :
    (Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι).map
      (closedFibreAdjunctionMap A f δ) = 0 := by
  rw [closedFibreAdjunctionMap, Adjunction.homEquiv_unit, Functor.map_comp,
    restrict_pushforward_eq_zero _ _ δ hδ, comp_zero]

/-- The two projections of the kernel of `biprod.desc left (-right)` agree after composing with
`left` and `right`. -/
private lemma kernel_biprod_desc_fst_comp_eq_snd_comp
    {C : Type*} [Category C] [Abelian C] {P Q H : C} (left : P ⟶ H) (right : Q ⟶ H) :
    (kernel.ι (biprod.desc left (-right)) ≫ biprod.fst) ≫ left =
      (kernel.ι (biprod.desc left (-right)) ≫ biprod.snd) ≫ right := by
  apply sub_eq_zero.mp
  simpa [biprod.desc_eq, Preadditive.comp_add, Category.assoc, sub_eq_add_neg]
    using kernel.condition (biprod.desc left (-right))

private lemma isIso_kernel_biprod_fst_of_isIso_right
    {C : Type*} [Category C] [Abelian C] {P Q H : C}
    (left : P ⟶ H) (right : Q ⟶ H) [IsIso right] :
    IsIso (kernel.ι (biprod.desc left (-right)) ≫ biprod.fst) := by
  let d := biprod.desc left (-right)
  let lift : P ⟶ kernel d := kernel.lift d
    (biprod.lift (𝟙 P) (left ≫ inv right)) (by simp [d])
  have hleft : lift ≫ kernel.ι d ≫ biprod.fst = 𝟙 P := by simp [lift]
  have hright : (kernel.ι d ≫ biprod.fst) ≫ lift = 𝟙 _ := by
    apply (cancel_mono (kernel.ι d)).mp
    apply biprod.hom_ext
    · simp [lift, Category.assoc]
    · have hrelation := kernel_biprod_desc_fst_comp_eq_snd_comp left right
      simp only [Category.assoc, Category.id_comp]
      rw [kernel.lift_ι_assoc, biprod.lift_snd]
      have h := congrArg (fun morphism => morphism ≫ inv right) hrelation
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h
  exact ⟨⟨lift, hright, hleft⟩⟩

lemma isIso_map_kernel_biprod_fst
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    {P Q H : C} (left : P ⟶ H) (right : Q ⟶ H)
    [IsIso (R.map right)] :
    IsIso (R.map (kernel.ι (biprod.desc left (-right)) ≫ biprod.fst)) := by
  let d := biprod.desc left (-right)
  let d' := biprod.desc (R.map left) (-R.map right)
  have : PreservesBinaryBiproducts R :=
    preservesBinaryBiproducts_of_preservesBinaryProducts R
  let b := R.mapBiprod P Q
  have hb : b.hom = Functor.biprodComparison R P Q := rfl
  have hcomm : R.map d = b.hom ≫ d' := by
    rw [hb]
    simp [d, d', biprod.desc_eq, Functor.map_add, Functor.map_comp, Functor.map_neg]
  let e : R.obj (kernel d) ≅ kernel d' :=
    PreservesKernel.iso R d ≪≫ kernel.mapIso (R.map d) d' b (Iso.refl _) (by simpa using hcomm)
  have hfac : R.map (kernel.ι d ≫ biprod.fst) = e.hom ≫ kernel.ι d' ≫ biprod.fst := by
    simp [e, Functor.map_comp, Category.assoc, hb]
  change IsIso (R.map (kernel.ι d ≫ biprod.fst))
  rw [hfac]
  have : IsIso (kernel.ι d' ≫ biprod.fst) :=
    isIso_kernel_biprod_fst_of_isIso_right (R.map left) (R.map right)
  infer_instance

private noncomputable abbrev restrictModuleMap {X : Scheme.{u}} (U : X.Opens)
    [IsOpenImmersion U.ι] {M N : X.Modules} (f : M ⟶ N) :
    M.restrict U.ι ⟶ N.restrict U.ι :=
  (Scheme.Modules.restrictFunctor U.ι).map f

private noncomputable def preparedExtension_restrictionIso
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (T : CoherentTriple A f)
    (P Q : PreparedExtension A f T) :
    P.F'.restrict (Stacks.Divisors.puncturedSpectrum A).ι ≅
      Q.F'.restrict (Stacks.Divisors.puncturedSpectrum A).ι := by
  let U := Stacks.Divisors.puncturedSpectrum A
  exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app P.F').trans P.alpha' |>.trans
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q.F').trans Q.alpha').symm

private lemma preparedExtension_restrictionIso_apply_eq_pullback
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {T : CoherentTriple A f} (P Q : PreparedExtension A f T)
    {G : (baseScheme A).Modules}
    (a : G ⟶ P.F') (b : G ⟶ Q.F')
    (h : restrictModuleMap (Stacks.Divisors.puncturedSpectrum A) a ≫
          (preparedExtension_restrictionIso A f T P Q).hom =
        restrictModuleMap (Stacks.Divisors.puncturedSpectrum A) b) :
    (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map a ≫ P.alpha'.hom =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map b ≫
        Q.alpha'.hom := by
  let j := (Stacks.Divisors.puncturedSpectrum A).ι
  let E := Scheme.Modules.restrictFunctorIsoPullback j
  dsimp [preparedExtension_restrictionIso] at h
  have hcomp := congrArg (fun z => z ≫ E.hom.app Q.F' ≫ Q.alpha'.hom) h
  have hE : E.inv.app Q.F' ≫ E.hom.app Q.F' = 𝟙 _ :=
    (E.app Q.F').inv_hom_id
  have htail : Q.alpha'.inv ≫
      (E.inv.app Q.F' ≫ (E.hom.app Q.F' ≫ Q.alpha'.hom)) = 𝟙 _ := by
    rw [← Category.assoc (E.inv.app Q.F') (E.hom.app Q.F') Q.alpha'.hom,
      hE, Category.id_comp, Q.alpha'.inv_hom_id]
  simp only [Category.assoc] at hcomp
  rw [htail, Category.comp_id] at hcomp
  change (Scheme.Modules.restrictFunctor j).map a ≫ E.hom.app P.F' ≫ P.alpha'.hom =
    (Scheme.Modules.restrictFunctor j).map b ≫ E.hom.app Q.F' ≫ Q.alpha'.hom at hcomp
  have hnatP := E.hom.naturality a
  have hnatQ := E.hom.naturality b
  rw [← Category.assoc, hnatP, Category.assoc,
    ← Category.assoc ((Scheme.Modules.restrictFunctor j).map b), hnatQ,
    Category.assoc] at hcomp
  exact (cancel_epi (E.hom.app G)).1 hcomp

/-- The comparison natural transformation identifying the pullback to the punctured closed fibre
with the restriction to the punctured spectrum followed by the pullback along the restricted
closed immersion. It is the first leg of `Stacks.Algebraization.PreparedExtension.compatible`,
given a name and an explicit type so that the composites it is built from are never unfolded. -/
noncomputable def puncturedClosedFibrePullbackOpen
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A) :
    Scheme.Modules.pullback ((puncturedClosedFibre A f).ι ≫ closedImmersion A f) ⟶
      Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι ⋙
        Scheme.Modules.pullback
          (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) :=
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)).symm).hom ≫
    (Scheme.Modules.pullbackComp
      (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A))
      (Stacks.Divisors.puncturedSpectrum A).ι).inv

/-- The comparison natural transformation identifying the pullback to the punctured closed fibre
with the pullback along the closed immersion followed by the restriction to the punctured closed
fibre. It is the second leg of `Stacks.Algebraization.PreparedExtension.compatible`. -/
noncomputable def puncturedClosedFibrePullbackClosed
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A) :
    Scheme.Modules.pullback ((puncturedClosedFibre A f).ι ≫ closedImmersion A f) ⟶
      Scheme.Modules.pullback (closedImmersion A f) ⋙
        Scheme.Modules.pullback (puncturedClosedFibre A f).ι :=
  (Scheme.Modules.pullbackComp (puncturedClosedFibre A f).ι (closedImmersion A f)).inv

instance isIso_puncturedClosedFibrePullbackClosed_app
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A) (F : (baseScheme A).Modules) :
    IsIso ((puncturedClosedFibrePullbackClosed A f).app F) := by
  change IsIso ((Scheme.Modules.pullbackComp (puncturedClosedFibre A f).ι
    (closedImmersion A f)).inv.app F)
  infer_instance

lemma preparedExtension_compatible'
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) :
    (puncturedClosedFibrePullbackOpen A f).app P.F' ≫
        (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map P.alpha'.hom ≫ T.alpha.hom =
      (puncturedClosedFibrePullbackClosed A f).app P.F' ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map P.alpha₀' :=
  (Category.assoc
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)).symm).hom.app P.F')
    ((Scheme.Modules.pullbackComp
        (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A))
        (Stacks.Divisors.puncturedSpectrum A).ι).inv.app P.F')
    ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map P.alpha'.hom ≫
      T.alpha.hom)).trans P.compatible

lemma preparedExtension_pullback_compat_apply
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) {G : (baseScheme A).Modules} (g : G ⟶ P.F') :
    (puncturedClosedFibrePullbackClosed A f).app G ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          ((Scheme.Modules.pullback (closedImmersion A f)).map g ≫ P.alpha₀') =
      (puncturedClosedFibrePullbackOpen A f).app G ≫
        (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map
          ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g ≫
            P.alpha'.hom) ≫ T.alpha.hom := by
  have hnat₀ :
      (Scheme.Modules.pullback ((puncturedClosedFibre A f).ι ≫ closedImmersion A f)).map g ≫
          (puncturedClosedFibrePullbackClosed A f).app P.F' =
        (puncturedClosedFibrePullbackClosed A f).app G ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            ((Scheme.Modules.pullback (closedImmersion A f)).map g) :=
    (puncturedClosedFibrePullbackClosed A f).naturality g
  have hnat₁ :
      (Scheme.Modules.pullback ((puncturedClosedFibre A f).ι ≫ closedImmersion A f)).map g ≫
          (puncturedClosedFibrePullbackOpen A f).app P.F' =
        (puncturedClosedFibrePullbackOpen A f).app G ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
              (Stacks.Divisors.puncturedSpectrum A))).map
            ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map g) :=
    (puncturedClosedFibrePullbackOpen A f).naturality g
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← hnat₀, Category.assoc,
    ← preparedExtension_compatible' A P, Category.assoc, ← Category.assoc, hnat₁,
    Category.assoc]

private lemma preparedExtension_closedFibreMap_restrict_eq
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {T : CoherentTriple A f} (P Q : PreparedExtension A f T)
    {G : (baseScheme A).Modules}
    (a : G ⟶ P.F') (b : G ⟶ Q.F')
    (hopen : (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map a ≫
        P.alpha'.hom =
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map b ≫
        Q.alpha'.hom) :
    (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        ((Scheme.Modules.pullback (closedImmersion A f)).map a ≫ P.alpha₀') =
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        ((Scheme.Modules.pullback (closedImmersion A f)).map b ≫ Q.alpha₀') := by
  apply (cancel_epi ((puncturedClosedFibrePullbackClosed A f).app G)).1
  rw [preparedExtension_pullback_compat_apply A P a,
    preparedExtension_pullback_compat_apply A Q b, hopen]

lemma regular_globalSections_injective
    {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T : CoherentTriple A f} (P : PreparedExtension A f T) :
    Function.Injective ((LinearMap.lsmul A
      ((moduleSpecΓFunctor (R := .of A).obj P.F').carrier)) f) := by
  have hreg := P.regular ⊤
  change Function.Injective (fun x : Γ(P.F', ⊤) =>
    ((baseScheme A).presheaf.map (homOfLE (le_top : (⊤ : (baseScheme A).Opens) ≤ ⊤)).op)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) • x)
  exact hreg

private lemma refinement_kernel_projection_compat
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (P Q : Y.Modules) (G : X.Modules)
    (e : P.restrict j ≅ Q.restrict j)
    (targetIso : Q.restrict j ≅ G) :
    let left := (Scheme.Modules.restrictAdjunction j).homEquiv P G
      (e.hom ≫ targetIso.hom)
    let right := (Scheme.Modules.restrictAdjunction j).homEquiv Q G targetIso.hom
    let d := biprod.desc left (-right)
    let a := kernel.ι d ≫ biprod.fst
    let b := kernel.ι d ≫ biprod.snd
    (Scheme.Modules.restrictFunctor j).map a ≫ e.hom =
      (Scheme.Modules.restrictFunctor j).map b := by
  dsimp only
  let adj := Scheme.Modules.restrictAdjunction j
  let left := adj.homEquiv P G (e.hom ≫ targetIso.hom)
  let right := adj.homEquiv Q G targetIso.hom
  let d := biprod.desc left (-right)
  let a := kernel.ι d ≫ biprod.fst
  let b := kernel.ι d ≫ biprod.snd
  have hrelation : a ≫ left = b ≫ right := kernel_biprod_desc_fst_comp_eq_snd_comp left right
  have hrelation' := congrArg (adj.homEquiv _ G).symm hrelation
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hrelation'
  change (Scheme.Modules.restrictFunctor j).map a ≫ e.hom =
    (Scheme.Modules.restrictFunctor j).map b
  exact (cancel_mono targetIso.hom).mp (by simpa [Category.assoc] using hrelation')

lemma mono_app_injective {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) [Mono φ] (V : X.Opens) : Function.Injective (φ.app V) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
    (Scheme.Modules.toPresheaf X).map_mono φ
  have : Mono (((Scheme.Modules.toPresheaf X).map φ).app (op V)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective
    (((Scheme.Modules.toPresheaf X).map φ).app (op V))).mp inferInstance

lemma regular_of_mono
    (A : Type u) [CommRing A] (f : A) {G H : (baseScheme A).Modules}
    (φ : G ⟶ H) [Mono φ]
    (hH : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(H, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) :
    ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) := by
  intro V
  exact IsSMulRegular.of_injective (φ.val.app (op V)).hom
    (mono_app_injective φ V) (hH V)

private lemma regular_of_mono_biprod
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (T : CoherentTriple A f) (P Q : PreparedExtension A f T)
    {G : (baseScheme A).Modules} (φ : G ⟶ P.F' ⊞ Q.F') [Mono φ] :
    ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) := by
  intro V
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro value hvalue
  have hproj : ∀ {Z : (baseScheme A).Modules} (ψ : G ⟶ Z),
      IsSMulRegular Γ(Z, V) ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) → ψ.app V value = 0 := by
    intro Z ψ hZ
    apply hZ.right_eq_zero_of_smul
    rw [← Scheme.Modules.Hom.app_smul, hvalue, map_zero]
  have hleft := hproj (φ ≫ biprod.fst) (P.regular V)
  have hright := hproj (φ ≫ biprod.snd) (Q.regular V)
  have htotal : φ.app V value = 0 := by
    have htotal : φ = (φ ≫ biprod.fst) ≫ biprod.inl +
        (φ ≫ biprod.snd) ≫ biprod.inr := by
      simpa only [Preadditive.comp_add, Category.assoc, Category.comp_id] using
        congrArg (fun morphism => φ ≫ morphism)
          (biprod.total (X := P.F') (Y := Q.F')).symm
    rw [htotal]
    change ((show P.F' ⟶ P.F' ⊞ Q.F' from biprod.inl).app V)
        ((φ ≫ biprod.fst).app V value) +
      ((show Q.F' ⟶ P.F' ⊞ Q.F' from biprod.inr).app V)
        ((φ ≫ biprod.snd).app V value) = 0
    rw [hleft, hright, map_zero, map_zero, add_zero]
  exact mono_app_injective φ V (htotal.trans (map_zero _).symm)

private lemma exists_coherent_refinement_over_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (T : CoherentTriple A f) (P Q : PreparedExtension A f T) :
    ∃ (G : (baseScheme A).Modules) (a : G ⟶ P.F') (b : G ⟶ Q.F'),
      G.IsCoherent ∧
      (∀ V : (baseScheme A).Opens,
        IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map
          (homOfLE (le_top : V ≤ ⊤)).op
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) ∧
      IsIso ((Scheme.Modules.restrictFunctor
        (Stacks.Divisors.puncturedSpectrum A).ι).map a) ∧
      IsIso ((Scheme.Modules.restrictFunctor
        (Stacks.Divisors.puncturedSpectrum A).ι).map b) ∧
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map a ≫
          P.alpha'.hom =
        (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map b ≫
          Q.alpha'.hom := by
  let j := (Stacks.Divisors.puncturedSpectrum A).ι
  let R := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  let e := preparedExtension_restrictionIso A f T P Q
  let targetIso : Q.F'.restrict j ≅ T.F :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app Q.F' ≪≫ Q.alpha'
  let left := adj.homEquiv P.F' T.F (e.hom ≫ targetIso.hom)
  let right := adj.homEquiv Q.F' T.F targetIso.hom
  let d := biprod.desc left (-right)
  let G := kernel d
  let a : G ⟶ P.F' := kernel.ι d ≫ biprod.fst
  let b : G ⟶ Q.F' := kernel.ι d ≫ biprod.snd
  have : IsLocallyNoetherian (baseScheme A) := inferInstance
  have : P.F'.IsCoherent := P.coherent
  have : Q.F'.IsCoherent := Q.coherent
  have : T.F.IsCoherent := T.coherent_F
  have : T.F.IsQuasicoherent := isQuasicoherent_of_isCoherent T.F
  have : (P.F' ⊞ Q.F').IsCoherent := isCoherent_biprod _ _ P.coherent Q.coherent
  have : (P.F' ⊞ Q.F').IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : ((Scheme.Modules.pushforward j).obj T.F).IsQuasicoherent := inferInstance
  have : G.IsQuasicoherent := inferInstance
  have hcoh : G.IsCoherent :=
    StacksDraft.AlgebraicGeometry.CoherentSubquotients.QuasicoherentSubmodule.isCoherent_of_mono
      (kernel.ι d)
  have hright : IsIso (R.map right) :=
    isIso_restrict_adjunctionMap_of_iso j Q.F' T.F targetIso
  have hleft : IsIso (R.map left) :=
    isIso_restrict_adjunctionMap_of_iso j P.F' T.F (e ≪≫ targetIso)
  have ha : IsIso (R.map a) := isIso_map_kernel_biprod_fst R left right
  have hrel : R.map a ≫ e.hom = R.map b :=
    refinement_kernel_projection_compat j P.F' Q.F' T.F e targetIso
  have hb : IsIso (R.map b) := by
    rw [← hrel]
    infer_instance
  have hopen : (Scheme.Modules.pullback j).map a ≫ P.alpha'.hom =
      (Scheme.Modules.pullback j).map b ≫ Q.alpha'.hom :=
    preparedExtension_restrictionIso_apply_eq_pullback A P Q a b hrel
  exact ⟨G, a, b, hcoh, regular_of_mono_biprod A f T P Q (kernel.ι d),
    ha, hb, hopen⟩

/-- The global sections of a coherent module supported at the closed point are annihilated by a
power of the maximal ideal: the submodule form of
`Stacks.Algebraization.maximalIdealPower_smul_eq_bot_of_isZero_restrict`. -/
lemma maximalIdealPower_smul_top_eq_bot
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (baseScheme A).Modules) (hcoh : _root_.SheafOfModules.IsCoherent F)
    (hF : IsZero ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).obj F)) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n •
      (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj F)) = ⊥ := by
  obtain ⟨n, hn⟩ :=
    maximalIdealPower_smul_eq_bot_of_isZero_restrict A F hcoh hF
  refine ⟨n, le_antisymm (Submodule.smul_le.mpr fun a ha v _ => ?_) bot_le⟩
  exact (Submodule.mem_bot _).mpr (hn a ha v)

lemma exists_compatible_coherent_refinement
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (T : CoherentTriple A f) (P Q : PreparedExtension A f T) :
    ∃ (G : (baseScheme A).Modules) (a : G ⟶ P.F') (b : G ⟶ Q.F'),
      G.IsCoherent ∧
      (∀ V : (baseScheme A).Opens,
        IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map
          (homOfLE (le_top : V ≤ ⊤)).op
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) ∧
      IsIso ((Scheme.Modules.restrictFunctor
        (Stacks.Divisors.puncturedSpectrum A).ι).map a) ∧
      IsIso ((Scheme.Modules.restrictFunctor
        (Stacks.Divisors.puncturedSpectrum A).ι).map b) ∧
      (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map a ≫
          P.alpha'.hom =
        (Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).map b ≫
          Q.alpha'.hom ∧
      (Scheme.Modules.pullback (closedImmersion A f)).map a ≫ P.alpha₀' =
        (Scheme.Modules.pullback (closedImmersion A f)).map b ≫ Q.alpha₀' := by
  obtain ⟨H, a, b, hH, hregH, ha, hb, hopen⟩ :=
    exists_coherent_refinement_over_puncturedSpectrum A f T P Q
  let i := closedImmersion A f
  let j := (Stacks.Divisors.puncturedSpectrum A).ι
  let j₀ := (puncturedClosedFibre A f).ι
  let L := Scheme.Modules.pullback i
  let R := Scheme.Modules.restrictFunctor j
  let δ := L.map a ≫ P.alpha₀' - L.map b ≫ Q.alpha₀'
  let d := closedFibreAdjunctionMap A f δ
  have : H.IsCoherent := hH
  have : T.F₀.IsCoherent := T.coherent_F₀
  have : T.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) Ideal.Quotient.mk_surjective
  have : IsFinite i := inferInstance
  have : ((Scheme.Modules.pushforward i).obj T.F₀).IsCoherent := inferInstance
  have hδ : (Scheme.Modules.restrictFunctor j₀).map δ = 0 := by
    have heq := preparedExtension_closedFibreMap_restrict_eq A P Q a b hopen
    have e := Scheme.Modules.restrictFunctorIsoPullback j₀
    have heq' : (Scheme.Modules.restrictFunctor j₀).map (L.map a ≫ P.alpha₀') =
        (Scheme.Modules.restrictFunctor j₀).map (L.map b ≫ Q.alpha₀') := by
      apply (cancel_mono (e.hom.app T.F₀)).mp
      rw [e.hom.naturality, e.hom.naturality, heq]
    simpa only [δ, Functor.map_sub, sub_eq_zero] using heq'
  have hd : R.map d = 0 := restrict_closedFibreAdjunctionMap_eq_zero A f δ hδ
  let G := kernel d
  let c : G ⟶ H := kernel.ι d
  have : G.IsCoherent := SheafOfModules.kernel_isCoherent d
  have hc : IsIso (R.map c) := isIso_restrict_kernel_ι_of_map_eq_zero j d hd
  have hclosed : L.map (c ≫ a) ≫ P.alpha₀' = L.map (c ≫ b) ≫ Q.alpha₀' := by
    apply sub_eq_zero.mp
    apply ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv G T.F₀).injective
    rw [Adjunction.homAddEquiv_zero]
    change closedFibreAdjunctionMap A f
      (L.map (c ≫ a) ≫ P.alpha₀' - L.map (c ≫ b) ≫ Q.alpha₀') = 0
    have hdiff : L.map (c ≫ a) ≫ P.alpha₀' - L.map (c ≫ b) ≫ Q.alpha₀' =
        L.map c ≫ δ := by simp [δ, Functor.map_comp, Category.assoc, Preadditive.comp_sub]
    rw [hdiff, closedFibreAdjunctionMap_comp]
    exact kernel.condition d
  refine ⟨G, c ≫ a, c ≫ b, inferInstance, regular_of_mono A f c hregH, ?_, ?_, ?_, hclosed⟩
  iterate 2 (rw [Functor.map_comp]; infer_instance)
  · simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun morphism => (Scheme.Modules.pullback j).map c ≫ morphism) hopen

end Stacks.Algebraization

end
