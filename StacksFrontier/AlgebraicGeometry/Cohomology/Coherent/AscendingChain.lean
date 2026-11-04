module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.OrderIsoNat
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Ascending chains of quasi-coherent submodules of a coherent sheaf

On a Noetherian scheme every ascending chain of quasi-coherent submodules of a coherent sheaf
of modules eventually stabilizes.

## Main results

* `AlgebraicGeometry.exists_eventually_constant_quasicoherentSubobjects` is the ascending chain
  condition for quasi-coherent subobjects of a coherent sheaf.

## Implementation notes

Submodules of a sheaf of modules are represented by categorical subobjects. A chain is a
monotone sequence of such subobjects, each of whose underlying sheaves is quasi-coherent, and
its eventual constancy expresses stabilization of the whole ascending chain rather than only of
consecutive terms.

The proof is local. On an affine chart `Spec A` of a Noetherian scheme a coherent sheaf becomes
the sheaf associated with a finite `A`-module `M`, and the quasi-coherent subobjects of that
sheaf correspond, through `AlgebraicGeometry.tildeEquiv` and the order isomorphism between
subobjects of equivalent objects, to the submodules of `M`; those satisfy the ascending chain
condition because `A` is Noetherian. A finite affine subcover turns the chartwise stabilization
indices into a single one, and `subobject_eq_of_restrictSubobject_eq` glues: an inclusion of
subobjects which is an isomorphism on each member of an open cover is an isomorphism, checked on
stalks.

## References

* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private noncomputable def modulesEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Y.Modules ≌ Z.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctor e.hom)
    (((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId (X := Y)).symm)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId (X := Z))

private noncomputable def quasicoherentModulesEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory := by
  let E := modulesEquivOfIso e
  let QY := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let QZ := SheafOfModules.isQuasicoherent Z.ringCatSheaf
  let F := ObjectProperty.lift QZ (QY.ι ⋙ E.functor) (fun M => by
    change ((Scheme.Modules.restrictFunctor e.inv).obj M.obj).IsQuasicoherent
    have : M.obj.IsQuasicoherent := M.property
    exact Scheme.Modules.isQuasicoherent_restrictFunctor e.inv M.obj)
  let G := ObjectProperty.lift QY (QZ.ι ⋙ E.inverse) (fun M => by
    change ((Scheme.Modules.restrictFunctor e.hom).obj M.obj).IsQuasicoherent
    have : M.obj.IsQuasicoherent := M.property
    exact Scheme.Modules.isQuasicoherent_restrictFunctor e.hom M.obj)
  exact CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk QY (E.unitIso.app M.obj))
      fun f => ObjectProperty.hom_ext _ (E.unitIso.hom.naturality f.hom))
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk QZ (E.counitIso.app M.obj))
      fun f => ObjectProperty.hom_ext _ (E.counitIso.hom.naturality f.hom))

/-- The subobject of `F|_Y` cut out by a subobject of `F`, along an open immersion `f : Y ⟶ X`.
Restriction preserves monomorphisms, so the restricted arrow still presents a subobject. -/
private noncomputable def restrictSubobject {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {F : X.Modules} (S : Subobject F) :
    Subobject ((Scheme.Modules.restrictFunctor f).obj F) :=
  have : Mono ((Scheme.Modules.restrictFunctor f).map S.arrow) :=
    mono_restrictFunctor_map f S.arrow
  Subobject.mk ((Scheme.Modules.restrictFunctor f).map S.arrow)

/-- A finite module over a Noetherian ring satisfies the ascending chain condition on
subobjects. -/
theorem _root_.ModuleCat.wellFoundedGT_subobject {R : Type u} [Ring R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : WellFoundedGT (Subobject M) := by
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro a
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition (α := Submodule R M)
    ⟨fun n => ModuleCat.subobjectModule M (a n), fun _ _ h =>
      (ModuleCat.subobjectModule M).monotone (a.monotone h)⟩
  exact ⟨n, fun m hnm => (ModuleCat.subobjectModule M).injective (hn m hnm)⟩

/-- Quasi-coherent subobjects of a pullback of `tilde M` along `Y ≅ Spec R` correspond to
subobjects of `M`. -/
private noncomputable def subobjectOrderIsoOfTilde {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (e : Y ≅ Spec R) (A : Y.Modules) (M : ModuleCat.{u} R)
    (hA : A ≅ (Scheme.Modules.pullback e.hom).obj (AlgebraicGeometry.tilde M))
    (hAQ : A.IsQuasicoherent) :
    Subobject (⟨A, hAQ⟩ : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) ≃o
      Subobject M := by
  let QY := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let Aq : QY.FullSubcategory := ⟨A, hAQ⟩
  let E := quasicoherentModulesEquivOfIso e
  let hAinv : A ≅ (modulesEquivOfIso e).inverse.obj (AlgebraicGeometry.tilde M) :=
    hA ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app (AlgebraicGeometry.tilde M)).symm
  let TQ : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨AlgebraicGeometry.tilde M, inferInstance⟩
  let hAq : Aq ≅ E.inverse.obj TQ := ObjectProperty.isoMk QY hAinv
  let j : E.functor.obj Aq ≅ TQ := E.functor.mapIso hAq ≪≫ E.counitIso.app TQ
  exact (Subobject.lowerEquivalence (MonoOver.congr Aq E)).toOrderIso.trans
    ((Subobject.mapIsoToOrderIso j).trans
      (Subobject.lowerEquivalence (MonoOver.congr M (tildeEquiv (R := R)))).toOrderIso.symm)

private theorem acc_quasicoherentSubobjects_of_finiteTilde
    {Y : Scheme.{u}} (R : CommRingCat.{u}) [IsNoetherianRing R]
    (e : Y ≅ Spec R) (A : Y.Modules) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hA : A ≅ (Scheme.Modules.pullback e.hom).obj (AlgebraicGeometry.tilde M))
    (G : ℕ → Subobject A) (hG : ∀ n, (G n : Y.Modules).IsQuasicoherent)
    (hmono : Monotone G) :
    ∃ n, ∀ m, n ≤ m → G m = G n := by
  let QY := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  have hAQ : A.IsQuasicoherent := QY.prop_of_iso hA.symm <| QY.prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app (AlgebraicGeometry.tilde M))
    (Scheme.Modules.isQuasicoherent_restrictFunctor e.hom (AlgebraicGeometry.tilde M))
  let Aq : QY.FullSubcategory := ⟨A, hAQ⟩
  let GQ (n : ℕ) : QY.FullSubcategory := ⟨(G n : Y.Modules), hG n⟩
  let GQarrow (n : ℕ) : GQ n ⟶ Aq :=
    ObjectProperty.homMk (X := GQ n) (Y := Aq) (G n).arrow
  have hGQmono (n : ℕ) : Mono (GQarrow n) :=
    (ObjectProperty.ι QY).mono_of_mono_map (inferInstanceAs (Mono (G n).arrow))
  let φ := subobjectOrderIsoOfTilde e A M hA hAQ
  have hfm : Monotone fun n => φ (Subobject.mk (GQarrow n)) := fun n m hnm =>
    φ.monotone <| Subobject.mk_le_mk_of_comm
      (ObjectProperty.homMk (X := GQ n) (Y := GQ m) (Subobject.ofLE (G n) (G m) (hmono hnm)))
      (ObjectProperty.hom_ext _ (Subobject.ofLE_arrow (h := hmono hnm)))
  obtain ⟨n, hn⟩ :=
    (ModuleCat.wellFoundedGT_subobject M).monotone_chain_condition ⟨_, hfm⟩
  refine ⟨n, fun m hnm => ?_⟩
  have hq : Subobject.mk (GQarrow n) = Subobject.mk (GQarrow m) := φ.injective (hn m hnm)
  let i := Subobject.isoOfMkEqMk (GQarrow n) (GQarrow m) hq
  have hcomm : (ObjectProperty.ι QY).map i.hom ≫ (G m).arrow = (G n).arrow := by
    show (ObjectProperty.ι QY).map
        (Subobject.ofMkLEMk (GQarrow n) (GQarrow m) (le_of_eq hq)) ≫
        (ObjectProperty.ι QY).map (GQarrow m) = (ObjectProperty.ι QY).map (GQarrow n)
    rw [← Functor.map_comp, Subobject.ofMkLEMk_comp]
  exact (Subobject.eq_of_comm ((ObjectProperty.ι QY).mapIso i) hcomm).symm

private theorem acc_quasicoherentSubobjects_on_affineChart
    {X : Scheme.{u}} [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (G : ℕ → Subobject F) (hG : ∀ n, (G n : X.Modules).IsQuasicoherent)
    (hmono : Monotone G) {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X)
    [IsOpenImmersion f] (M : ModuleCat.{u} (CommRingCat.of Γ(X, f.opensRange)))
    [Module.Finite Γ(X, f.opensRange) M]
    (hmodel : F.restrict f.opensRange.ι ≅
      (Scheme.Modules.pullback (isAffineOpen_opensRange f).isoSpec.hom).obj
        (AlgebraicGeometry.tilde M)) :
    ∃ n, ∀ m, n ≤ m → restrictSubobject f (G m) = restrictSubobject f (G n) := by
  let U := f.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange f
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let r := f.isoOpensRange
  let e : Y ≅ Spec (CommRingCat.of Γ(X, U)) := r ≪≫ hU.isoSpec
  let Ff := Scheme.Modules.restrictFunctor f
  let A : Y.Modules := Ff.obj F
  let H (n : ℕ) : Subobject A := restrictSubobject f (G n)
  have hHqc (n : ℕ) : (H n : Y.Modules).IsQuasicoherent := by
    have : (G n : X.Modules).IsQuasicoherent := hG n
    have : Mono ((Scheme.Modules.restrictFunctor f).map (G n).arrow) :=
      mono_restrictFunctor_map f (G n).arrow
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (Ff.map (G n).arrow)).symm
      (Scheme.Modules.isQuasicoherent_restrictFunctor f (G n))
  have hHmono' : Monotone H := by
    intro n m hnm
    have : Mono ((Scheme.Modules.restrictFunctor f).map (G n).arrow) :=
      mono_restrictFunctor_map f (G n).arrow
    have : Mono ((Scheme.Modules.restrictFunctor f).map (G m).arrow) :=
      mono_restrictFunctor_map f (G m).arrow
    show Subobject.mk (Ff.map (G n).arrow) ≤ Subobject.mk (Ff.map (G m).arrow)
    exact Subobject.mk_le_mk_of_comm (Ff.map (Subobject.ofLE (G n) (G m) (hmono hnm)))
      (by rw [← Functor.map_comp, Subobject.ofLE_arrow])
  have hA : A ≅ (Scheme.Modules.pullback e.hom).obj (AlgebraicGeometry.tilde M) :=
    ((Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι f)).symm ≪≫
      (Scheme.Modules.restrictFunctorComp r.hom U.ι)).app F ≪≫
      (Scheme.Modules.restrictFunctor r.hom).mapIso hmodel ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback r.hom).app
        ((Scheme.Modules.pullback hU.isoSpec.hom).obj (AlgebraicGeometry.tilde M)) ≪≫
      (Scheme.Modules.pullbackComp r.hom hU.isoSpec.hom).app (AlgebraicGeometry.tilde M)
  exact acc_quasicoherentSubobjects_of_finiteTilde
    (CommRingCat.of Γ(X, U)) e A M hA H hHqc hHmono'

/-- If two nested subobjects `A ≤ B` of `F` have the same restriction along an open immersion `f`,
then the restriction along `f` of the inclusion of `A` in `B` is an isomorphism. -/
private lemma isIso_restrictFunctor_map_ofLE {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {F : X.Modules} {A B : Subobject F} (hle : A ≤ B)
    (h : restrictSubobject f B = restrictSubobject f A) :
    IsIso ((Scheme.Modules.restrictFunctor f).map (Subobject.ofLE A B hle)) := by
  have : Mono ((Scheme.Modules.restrictFunctor f).map A.arrow) :=
    mono_restrictFunctor_map f A.arrow
  have : Mono ((Scheme.Modules.restrictFunctor f).map B.arrow) :=
    mono_restrictFunctor_map f B.arrow
  have hAB : Subobject.mk ((Scheme.Modules.restrictFunctor f).map A.arrow) =
      Subobject.mk ((Scheme.Modules.restrictFunctor f).map B.arrow) := by
    simpa [restrictSubobject] using h.symm
  have hfactor : (Scheme.Modules.restrictFunctor f).map (Subobject.ofLE A B hle) =
      (Subobject.isoOfMkEqMk _ _ hAB).hom := by
    apply (cancel_mono ((Scheme.Modules.restrictFunctor f).map B.arrow)).mp
    rw [← Functor.map_comp, Subobject.ofLE_arrow]
    show (Scheme.Modules.restrictFunctor f).map A.arrow =
      (Subobject.ofMkLEMk _ _ hAB.le) ≫ (Scheme.Modules.restrictFunctor f).map B.arrow
    rw [Subobject.ofMkLEMk_comp]
  rw [hfactor]
  infer_instance

private lemma subobject_eq_of_restrictSubobject_eq
    {X : Scheme.{u}} (F : X.Modules) (A B : Subobject F) (hle : A ≤ B) (𝒰 : X.OpenCover)
    (hlocal : ∀ i, restrictSubobject (𝒰.f i) B = restrictSubobject (𝒰.f i) A) :
    A = B := by
  let q : (A : X.Modules) ⟶ (B : X.Modules) := Subobject.ofLE A B hle
  let FA : TopCat.Sheaf Ab.{u} X := ⟨(A : X.Modules).presheaf, (A : X.Modules).isSheaf⟩
  let FB : TopCat.Sheaf Ab.{u} X := ⟨(B : X.Modules).presheaf, (B : X.Modules).isSheaf⟩
  let qsh : FA ⟶ FB := (TopCat.Sheaf.forget Ab.{u} X).preimage q.mapPresheaf
  have hunderlying : (TopCat.Sheaf.forget Ab.{u} X).map qsh = q.mapPresheaf :=
    (TopCat.Sheaf.forget Ab.{u} X).map_preimage _
  have hqsh : IsIso qsh := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    let i := 𝒰.idx x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    rw [← hy]
    let f := 𝒰.f i
    let E := Scheme.Modules.restrictStalkNatIso f y
    let L := Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf (𝒰.X i) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y
    have := isIso_restrictFunctor_map_ofLE f hle (hlocal i)
    have : IsIso (L.map q) := Functor.map_isIso
      (Scheme.Modules.toPresheaf (𝒰.X i) ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y)
      ((Scheme.Modules.restrictFunctor f).map q)
    have hηcomp : IsIso (E.hom.app (A : X.Modules) ≫
        (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map q) := by
      rw [← E.hom.naturality q]
      infer_instance
    have hηcomp' : IsIso (E.hom.app (A : X.Modules) ≫
        (TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map q.mapPresheaf) := by
      simpa only [Functor.comp_obj, Functor.comp_map, Scheme.Modules.toPresheaf_obj,
        Scheme.Modules.toPresheaf_map] using hηcomp
    show IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map
      ((TopCat.Sheaf.forget Ab.{u} X).map qsh))
    rw [hunderlying]
    exact (isIso_comp_left_iff (E.hom.app (A : X.Modules)) _).mp hηcomp'
  have hqP : IsIso q.mapPresheaf := by
    rw [← hunderlying]
    exact Functor.map_isIso (TopCat.Sheaf.forget Ab.{u} X) qsh
  have hq : IsIso q :=
    (isIso_iff_of_reflects_iso q (Scheme.Modules.toPresheaf X)).mp (by simpa using hqP)
  exact Subobject.eq_of_comm (asIso q) (Subobject.ofLE_arrow hle)

/-- **Stacks Project, Tag 01Y8.** An ascending chain of quasi-coherent submodules of a coherent
sheaf on a Noetherian scheme eventually stabilizes. -/
@[stacks 01Y8]
public theorem exists_eventually_constant_quasicoherentSubobjects
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (G : ℕ → Subobject F) (hG : ∀ n, (G n : X.Modules).IsQuasicoherent)
    (hmono : Monotone G) :
    ∃ n, ∀ m, n ≤ m → G m = G n := by
  let 𝒰 := X.affineCover.finiteSubcover
  have hstab (i : 𝒰.I₀) : ∃ n, ∀ m, n ≤ m →
      restrictSubobject (𝒰.f i) (G m) = restrictSubobject (𝒰.f i) (G n) := by
    let U := (𝒰.f i).opensRange
    have : IsAffine (𝒰.X i) := by
      dsimp [𝒰]
      infer_instance
    obtain ⟨M, hM, hmodel⟩ := Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isCoherent
      F U (isAffineOpen_opensRange _)
    have : Module.Finite Γ(X, U) M := hM
    exact acc_quasicoherentSubobjects_on_affineChart F G hG hmono
      (𝒰.f i) M (Classical.choice hmodel)
  choose N hN using hstab
  have hN₀ (i : 𝒰.I₀) : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨Finset.univ.sup N, fun m hm => (subobject_eq_of_restrictSubobject_eq F _ (G m)
    (hmono hm) 𝒰 fun i => ?_).symm⟩
  exact (hN i m ((hN₀ i).trans hm)).trans (hN i _ (hN₀ i)).symm

end AlgebraicGeometry
