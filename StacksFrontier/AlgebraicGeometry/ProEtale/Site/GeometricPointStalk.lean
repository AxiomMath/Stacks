module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.StrictlyHenselian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Classical points of the small pro-étale site

Let `S` be a scheme and `s` a geometric point of `S`. The strict henselization of `S` at `s`,
that is the spectrum of the étale local ring `𝒪_{S, s}^{sh}`, is an object of the small
pro-étale site of `S`, it carries a canonical lift of `s`, and evaluating a presheaf on the
small pro-étale site at that object computes the stalk of the presheaf at `s`, naturally in the
presheaf.

## Main definitions

* `AlgebraicGeometry.proetalePointFiber`: the functor sending an object of the small pro-étale
  site to the set of lifts of the geometric point to it.
* `AlgebraicGeometry.proetaleStalk`: the stalk of a presheaf on the small pro-étale site at the
  geometric point, the colimit over the category of pro-étale neighbourhoods.
* `AlgebraicGeometry.strictHenselizationProEt`: the strict henselization as an object of the
  small pro-étale site.
* `AlgebraicGeometry.strictHenselizationSectionsEquivStalk`: the comparison of sections over the
  strict henselization with the stalk.

## Main results

* `AlgebraicGeometry.weaklyEtale_strictHenselizationToBase`: **Stacks Project, Tag 0993.** The
  structure morphism of the strict henselization is weakly étale, so the strict henselization is
  an object of the small pro-étale site.
* `AlgebraicGeometry.isInitial_strictHenselizationPoint`: Olivier's theorem in geometric form —
  the strict henselization with its canonical lift is an initial pro-étale neighbourhood.
* `AlgebraicGeometry.strictHenselizationSectionsEquivStalk`, `_apply` and `_natural`: sections
  over the strict henselization are canonically the stalk, by the colimit insertion at the
  canonical neighbourhood, naturally in the presheaf.

## Implementation notes

Membership in the small pro-étale site is weak étaleness of the structure morphism, which is how
Mathlib's `AlgebraicGeometry.Scheme.ProEt` is defined, so the object claim of the source is
exactly `weaklyEtale_strictHenselizationToBase`. The source's "canonical isomorphism" is
produced as the colimit insertion at the canonical neighbourhood: the construction is named,
`strictHenselizationSectionsEquivStalk_apply` identifies it with that insertion, and
`strictHenselizationSectionsEquivStalk_natural` is the functoriality the source asks for.

The lifting property behind initiality is
`exists_lift_of_strictlyHenselian_of_weaklyEtale`: over the spectrum of a strictly henselian
local ring a weakly étale morphism admits a unique lift through any prescribed lift over the
closed point. It rests on Olivier's theorem in the form
`bijective_algebraMap_of_weaklyEtale_of_isLocalHom` (Stacks, Tag 092Z) applied to the stalk of
the fibre product at the chosen point.

## References

* [Stacks Project, Tag 0993](https://stacks.math.columbia.edu/tag/0993)
* [Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z)
* [Stacks Project, Tag 094Z](https://stacks.math.columbia.edu/tag/094Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u v

/-! ### Transport of strict henselianity along a ring isomorphism -/

/-- A ring isomorphic to a strictly henselian local ring is a strictly henselian local ring. -/
theorem StrictlyHenselianLocalRing.of_ringEquiv {R T : Type*} [CommRing R] [CommRing T]
    [StrictlyHenselianLocalRing R] (e : R ≃+* T) : StrictlyHenselianLocalRing T := by
  let : IsLocalRing T := e.isLocalRing
  let : HenselianLocalRing T := HenselianLocalRing.of_ringEquiv e
  let : IsSepClosed (ResidueField T) := IsSepClosed.of_ringEquiv (ResidueField.mapEquiv e).symm
  exact ⟨⟩

/-- A localization is weakly étale as an algebra. -/
theorem Algebra.WeaklyEtale.of_isLocalization (R : Type u) (T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] (M : Submonoid R) [IsLocalization M T] : Algebra.WeaklyEtale R T :=
  (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} R).1 T M

namespace AlgebraicGeometry

/-! ### Weak étaleness of the canonical morphism from a stalk -/

/-- The spectrum of a weakly étale ring homomorphism is a weakly étale morphism of schemes. -/
theorem weaklyEtale_specMap {R T : CommRingCat.{u}} (f : R ⟶ T)
    (h : @Algebra.WeaklyEtale R T _ _ f.hom.toAlgebra) : WeaklyEtale (Spec.map f) := by
  let : Algebra R T := f.hom.toAlgebra
  refine (weaklyEtale_iff _).mpr ⟨Flat.SpecMap_iff.mpr ?_, ?_⟩
  · exact RingHom.flat_algebraMap_iff.mpr h.flat
  · rw [show f = CommRingCat.ofHom (algebraMap R T) from rfl, diagonal_SpecMap R T]
    refine MorphismProperty.comp_mem @Flat _ _ ?_ inferInstance
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact h.flat_lmul'

/-- The canonical morphism from the spectrum of a local ring of a scheme is weakly étale: on an
affine open neighbourhood it is the spectrum of a localization of the sections there. -/
theorem weaklyEtale_fromSpecStalk (X : Scheme.{u}) (x : X) :
    WeaklyEtale (X.fromSpecStalk x) := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  change WeaklyEtale (hU.fromSpecStalk hx)
  dsimp only [IsAffineOpen.fromSpecStalk]
  have hwe : WeaklyEtale (Spec.map (X.presheaf.germ U x hx)) := by
    refine weaklyEtale_specMap _ ?_
    let : Algebra Γ(X, U) ↥(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        ↥(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    exact Algebra.WeaklyEtale.of_isLocalization _ _
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/-! ### Lifting along a weakly étale morphism over a strictly henselian local ring -/

/-- A morphism out of the spectrum of a local ring hitting a given point factors through the
canonical morphism from the local ring at that point. -/
theorem exists_comp_fromSpecStalk_eq {T : CommRingCat.{u}} [IsLocalRing T] {X : Scheme.{u}}
    (f : Spec T ⟶ X) (x : X) (hx : f (closedPoint T) = x) :
    ∃ g : Spec T ⟶ Spec (X.presheaf.stalk x), g ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨Spec.map (Scheme.stalkClosedPointTo f), Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

/-- Over a strictly henselian local base, a weakly étale morphism induces an isomorphism from the
spectrum of the local ring at any point over the closed point. -/
private theorem isIso_fromSpecStalk_comp_of_weaklyEtale {R : Type u} [CommRing R]
    [StrictlyHenselianLocalRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R)) [WeaklyEtale π]
    (y : Z) (hy : π y = closedPoint (CommRingCat.of R)) :
    IsIso (Z.fromSpecStalk y ≫ π) := by
  let R₀ := (Spec (.of R)).presheaf.stalk (π y)
  let T₀ := Z.presheaf.stalk y
  let e₀ : R₀ ≃+* R :=
    ((Spec (.of R)).presheaf.stalkCongr (Inseparable.of_eq hy)).commRingCatIsoToRingEquiv.trans
      (stalkClosedPointIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let : StrictlyHenselianLocalRing R₀ := StrictlyHenselianLocalRing.of_ringEquiv e₀.symm
  let : Algebra R₀ T₀ := (π.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap R₀ T₀) := inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have hk : Algebra.WeaklyEtale R₀ T₀ :=
    (weaklyEtale_iff_stalkMap_weaklyEtale π).mp ‹WeaklyEtale π› y
  have : IsIso (π.stalkMap y) := (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_algebraMap_of_weaklyEtale_of_isLocalHom _ _ hk)
  have : IsIso ((Spec (.of R)).fromSpecStalk (π y)) := by
    rw [hy, ← Spec_stalkClosedPointIso]
    infer_instance
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
  infer_instance

/-- **The unique lifting property of weakly étale morphisms over a strictly henselian local
ring.** Let `f : Y ⟶ X` be weakly étale and let `g : Spec R ⟶ X` with `R` strictly henselian
local. Given a morphism `p : Spec K ⟶ Spec R` hitting the closed point and a lift `t` of
`p ≫ g` through `f`, there is a unique lift of `g` through `f` restricting to `t` along `p`.

By Olivier's theorem (Stacks, Tag 092Z) the projection from the fibre product `Y ×_X Spec R` to
`Spec R` induces an isomorphism on local rings at the point determined by `t`, whence a section
of that projection from which the lift is read off. -/
@[ega "IV 18.5.11" "special case",
  ega "IV 18.8.1" "(a)⇒(c)",
  sga "3 X 4.5" "special case",
  sga "3 XI 1.11" "special case"]
theorem exists_lift_of_strictlyHenselian_of_weaklyEtale
    {R K : Type u} [CommRing R] [StrictlyHenselianLocalRing R] [CommRing K] [IsLocalRing K]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] (g : Spec (.of R) ⟶ X)
    (p : Spec (.of K) ⟶ Spec (.of R)) (hp : p (closedPoint K) = closedPoint (CommRingCat.of R))
    (t : Spec (.of K) ⟶ Y) (ht : t ≫ f = p ≫ g) :
    ∃! q : Spec (.of R) ⟶ Y, q ≫ f = g ∧ p ≫ q = t := by
  let Z := pullback f g
  let π₁ : Z ⟶ Y := pullback.fst f g
  let π₂ : Z ⟶ Spec (.of R) := pullback.snd f g
  let z : Spec (.of K) ⟶ Z := pullback.lift t p ht
  let y : Z := z (closedPoint K)
  have hy : π₂ y = closedPoint (CommRingCat.of R) := by
    change (z ≫ π₂) (closedPoint K) = _
    rw [pullback.lift_snd, hp]
  have : WeaklyEtale π₂ := inferInstanceAs (WeaklyEtale (pullback.snd f g))
  let a : Spec (Z.presheaf.stalk y) ⟶ Spec (.of R) := Z.fromSpecStalk y ≫ π₂
  have : IsIso a := isIso_fromSpecStalk_comp_of_weaklyEtale π₂ y hy
  let qZ : Spec (.of R) ⟶ Z := inv a ≫ Z.fromSpecStalk y
  have hsection : qZ ≫ π₂ = 𝟙 _ := (Category.assoc _ _ _).trans (IsIso.inv_hom_id a)
  have hpoint : p ≫ qZ = z := by
    obtain ⟨b, hb⟩ := exists_comp_fromSpecStalk_eq z y rfl
    have hba : b ≫ a = p := by
      dsimp only [a]
      rw [← Category.assoc, hb]
      exact pullback.lift_snd t p ht
    dsimp only [qZ]
    rw [← hba, Category.assoc, IsIso.hom_inv_id_assoc, hb]
  refine ⟨qZ ≫ π₁, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsection, Category.id_comp]
  · rw [← Category.assoc, hpoint]
    exact pullback.lift_fst t p ht
  · intro q hq
    let q' : Spec (.of R) ⟶ Z := pullback.lift q (𝟙 _) (by simpa using hq.1)
    have hq'section : q' ≫ π₂ = 𝟙 _ := pullback.lift_snd _ _ _
    have hq'point : p ≫ q' = z := by
      apply pullback.hom_ext <;>
        simp only [q', z, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, hq.2]
    have hq'y : q' (closedPoint (CommRingCat.of R)) = y := by
      rw [← hp]
      exact congrArg (fun e : Spec (.of K) ⟶ Z => e (closedPoint K)) hq'point
    obtain ⟨b, hb⟩ := exists_comp_fromSpecStalk_eq q' y hq'y
    have hba : b ≫ a = 𝟙 _ := by
      dsimp only [a]
      rw [← Category.assoc, hb, hq'section]
    have hq'eq : q' = qZ := by rw [← hb, IsIso.eq_inv_of_inv_hom_id hba]
    rw [← hq'eq]
    exact (pullback.lift_fst _ _ _).symm

/-! ### The strict henselization as a classical point of the pro-étale site -/

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The étale local ring at a geometric point is strictly henselian: it is isomorphic to the
strict henselization of the ordinary local ring at the image point. -/
@[sga "4 VIII 4.4" "A^hs, special case", sga "4½ Arcata 2.3.1" "special case"]
instance strictlyHenselianLocalRing_etaleLocalRing :
    StrictlyHenselianLocalRing ↥(etaleLocalRing B S hS s) :=
  StrictlyHenselianLocalRing.of_ringEquiv (etaleLocalRingEquivStrictHenselization B S hS s)

/-- Geometric evaluation of étale germs is a local homomorphism: through the identification with
the strict henselization it is the residue map followed by field embeddings. -/
instance isLocalHom_structureSheafStalkToGeometricField :
    IsLocalHom (structureSheafStalkToGeometricField B S hS s) := by
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let κsep := separableClosure (ResidueField R) s.residueField
  let T := geometricHenselizationTower S s
  let e := (etaleLocalRing_strictHenselization_canonical B S hS s T).val
  let φ : T.strictHenselization →+* s.residueField :=
    κsep.val.toRingHom.comp
      (T.strictHenselizationResidueEquiv.symm.toRingHom.comp (residue T.strictHenselization))
  have hφ : structureSheafStalkToGeometricField B S hS s = φ.comp e.symm.toRingHom := by
    ext a
    have ha := (etaleLocalRing_strictHenselization_canonical B S hS s T).property.2 (e.symm a)
    change structureSheafStalkToGeometricField B S hS s (e (e.symm a)) = φ (e.symm a) at ha
    change structureSheafStalkToGeometricField B S hS s a = φ (e.symm a)
    simpa only [RingEquiv.apply_symm_apply] using ha
  rw [hφ]
  have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
  have : IsLocalHom T.strictHenselizationResidueEquiv.symm.toRingHom :=
    IsLocalHom.of_surjective _ T.strictHenselizationResidueEquiv.symm.surjective
  have : IsLocalHom (T.strictHenselizationResidueEquiv.symm.toRingHom.comp
      (residue T.strictHenselization)) := RingHom.isLocalHom_comp _ _
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  exact RingHom.isLocalHom_comp _ _

/-- **Stacks Project, Tag 0993.** The canonical morphism from the strict henselization of `S` at
a geometric point `s` is weakly étale, so the strict henselization is an object of the small
pro-étale site of `S`. It is the spectrum of an ind-étale ring map followed by the canonical
morphism from the local ring at the image of `s`. -/
@[stacks 0993 "the pro-étale object"]
theorem weaklyEtale_strictHenselizationToBase :
    WeaklyEtale (strictHenselizationToBase B S hS s) := by
  have halg : Algebra.WeaklyEtale ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      ↥(etaleLocalRing B S hS s) :=
    Algebra.weaklyEtale_of_ind_etale (indEtale_etaleLocalRing B S hS s)
  have hspec : WeaklyEtale (Spec.map (CommRingCat.ofHom
      (structureSheafStalkFromLocalRing B S hS s))) := by
    refine weaklyEtale_specMap _ ?_
    rwa [show (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)).hom.toAlgebra =
      etaleLocalRingAlgebra B S hS s from (algebraMap_etaleLocalRing B S hS s).symm ▸ rfl]
  have : WeaklyEtale (S.fromSpecStalk (s.hom (closedPoint s.residueField))) :=
    weaklyEtale_fromSpecStalk S _
  change WeaklyEtale (Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫
    S.fromSpecStalk (s.hom (closedPoint s.residueField)))
  infer_instance

/-- The strict henselization of `S` at a geometric point, as an object of the small pro-étale
site of `S`. -/
def strictHenselizationProEt : S.ProEt :=
  letI : WeaklyEtale (strictHenselizationToBase B S hS s) :=
    weaklyEtale_strictHenselizationToBase B S hS s
  Scheme.ProEt.mk (strictHenselizationToBase B S hS s)

/-! ### Stalks on the small pro-étale site at a classical point -/

/-- Lifts of a geometric point to the objects of the small pro-étale site: the pro-étale
neighbourhoods of the point are the elements of this functor. -/
abbrev proetalePointFiber : S.ProEt ⥤ Type u :=
  Scheme.ProEt.forget S ⋙ coyoneda.obj (op (Over.mk s.hom))

/-- The stalk of a presheaf on the small pro-étale site of `S` at a geometric point: the colimit
of its sections over the category of pro-étale neighbourhoods of the point. -/
abbrev proetaleStalk (F : (S.ProEt)ᵒᵖ ⥤ Type (max (u + 1) v)) : Type (max (u + 1) v) :=
  colimit ((Functor.Elements.π (proetalePointFiber S s)).op ⋙ F)

/-- The strict henselization with its canonical lift, as a pro-étale neighbourhood of the
geometric point. -/
def strictHenselizationPoint :
    (proetalePointFiber S s).obj (strictHenselizationProEt B S hS s) :=
  Over.homMk (geometricPointToStrictHenselization B S hS s)
    (geometricPointToStrictHenselization_comp B S hS s)

/-- **Olivier's theorem in geometric form.** The strict henselization at a geometric point, with
its canonical lift, is an initial pro-étale neighbourhood of that point: every pro-étale
neighbourhood receives a unique morphism from it over `S` and under the geometric point. -/
def isInitial_strictHenselizationPoint :
    IsInitial (C := (proetalePointFiber S s).Elements)
      ((proetalePointFiber S s).elementsMk (strictHenselizationProEt B S hS s)
        (strictHenselizationPoint B S hS s)) := by
  have hp : geometricPointToStrictHenselization B S hS s (closedPoint s.residueField) =
      closedPoint (CommRingCat.of ↥(etaleLocalRing B S hS s)) := by
    let : IsLocalHom
        (CommRingCat.ofHom (structureSheafStalkToGeometricField B S hS s)).hom :=
      isLocalHom_structureSheafStalkToGeometricField B S hS s
    exact Spec_closedPoint
  have h (U : (proetalePointFiber S s).Elements) :
      ∃! q : strictHenselization B S hS s ⟶ U.obj.left,
        q ≫ U.obj.hom = strictHenselizationToBase B S hS s ∧
          geometricPointToStrictHenselization B S hS s ≫ q = U.val.left :=
    exists_lift_of_strictlyHenselian_of_weaklyEtale U.obj.hom
      (strictHenselizationToBase B S hS s) (geometricPointToStrictHenselization B S hS s) hp
      U.val.left <| (Over.w U.val).trans (geometricPointToStrictHenselization_comp B S hS s).symm
  let q (U : (proetalePointFiber S s).Elements) :
      (proetalePointFiber S s).elementsMk (strictHenselizationProEt B S hS s)
        (strictHenselizationPoint B S hS s) ⟶ U :=
    ⟨MorphismProperty.Over.homMk (h U).choose (h U).choose_spec.1.1,
      Over.OverMorphism.ext (h U).choose_spec.1.2⟩
  exact IsInitial.ofUniqueHom q fun U m => Functor.Elements.hom_ext <|
    MorphismProperty.Over.Hom.ext <|
    (h U).choose_spec.2 _ ⟨MorphismProperty.Over.w m.hom, congrArg (fun f => f.left) m.map_val⟩

/-- **Stacks Project, Tag 0993.** Sections of a presheaf on the small pro-étale site over the
strict henselization at a geometric point are canonically the stalk of the presheaf at that
geometric point. -/
@[stacks 0993 "the stalk comparison"]
def strictHenselizationSectionsEquivStalk (F : (S.ProEt)ᵒᵖ ⥤ Type (max (u + 1) v)) :
    F.obj (op (strictHenselizationProEt B S hS s)) ≃ proetaleStalk S s F :=
  Equiv.ofBijective
    (colimit.ι ((Functor.Elements.π (proetalePointFiber S s)).op ⋙ F)
      (op ((proetalePointFiber S s).elementsMk (strictHenselizationProEt B S hS s)
        (strictHenselizationPoint B S hS s))))
    ((ConcreteCategory.isIso_iff_bijective _).1 <|
      (colimit.isColimit ((Functor.Elements.π (proetalePointFiber S s)).op ⋙ F))
        |>.isIso_ι_app_of_isTerminal _ (isInitial_strictHenselizationPoint B S hS s).op)

/-- **Stacks Project, Tag 0993.** The comparison of sections over the strict henselization with
the stalk is the colimit insertion at the canonical pro-étale neighbourhood; this is what makes
it canonical. -/
@[stacks 0993 "the canonical stalk comparison"]
theorem strictHenselizationSectionsEquivStalk_apply
    (F : (S.ProEt)ᵒᵖ ⥤ Type (max (u + 1) v))
    (x : F.obj (op (strictHenselizationProEt B S hS s))) :
    strictHenselizationSectionsEquivStalk B S hS s F x =
      colimit.ι ((Functor.Elements.π (proetalePointFiber S s)).op ⋙ F)
        (op ((proetalePointFiber S s).elementsMk (strictHenselizationProEt B S hS s)
        (strictHenselizationPoint B S hS s))) x :=
  rfl

/-- **Stacks Project, Tag 0993.** The comparison of sections over the strict henselization with
the stalk is functorial in the presheaf. -/
@[stacks 0993 "functoriality of the stalk comparison"]
theorem strictHenselizationSectionsEquivStalk_natural
    {F G : (S.ProEt)ᵒᵖ ⥤ Type (max (u + 1) v)} (α : F ⟶ G)
    (x : F.obj (op (strictHenselizationProEt B S hS s))) :
    strictHenselizationSectionsEquivStalk B S hS s G
        (α.app (op (strictHenselizationProEt B S hS s)) x) =
      colim.map (Functor.whiskerLeft (Functor.Elements.π (proetalePointFiber S s)).op α)
        (strictHenselizationSectionsEquivStalk B S hS s F x) := by
  rw [strictHenselizationSectionsEquivStalk_apply, strictHenselizationSectionsEquivStalk_apply]
  exact (ConcreteCategory.congr_hom
    (colimit.ι_map (Functor.whiskerLeft (Functor.Elements.π (proetalePointFiber S s)).op α)
      (op ((proetalePointFiber S s).elementsMk (strictHenselizationProEt B S hS s)
        (strictHenselizationPoint B S hS s)))) x).symm

end AlgebraicGeometry

end
