module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.MinimalVersal.Basic
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.VersalObject.MinimalVersalDescent
public import StacksFrontier.RingTheory.Noetherian.Endomorphism

/-!
# The base of a smallest descent is a retract

Let `ξ` be a versal formal object of a category cofibered in groupoids over `𝒞_Λ` and let
`ξ' → ξ` be a smallest descent of it in the sense of Stacks 06T2, lying over a complete local
subalgebra `R' ⊂ R = ξ.base`. Then the inclusion `R' → R` admits a left inverse, so `R` is the
direct sum of `R'` and an ideal as an additive group. Both facts are what the proof of Stacks
06T3 uses, and they are proved there.

The retraction is produced as follows. The morphism `\underline{R}|_{𝒞_Λ} → F` associated to
`ξ` is smooth, because `ξ` is versal. The zeroth adic truncations of `R` and `R'` are both the
residue field, so the inclusion identifies them; that gives an Artinian point of `R` under
which the zeroth level of `ξ'` lifts to `\underline{R}|_{𝒞_Λ}`. Smoothness then lifts `ξ'`
level by level, producing a formal object `X` of `\underline{R}|_{𝒞_Λ}` whose image under the
associated morphism is isomorphic to `ξ'` over `R'`. Composing with the canonical morphism
`ξ → `(image of `X`) of `Deformation.nonempty_hom_completionMap_obj` gives a morphism
`f : ξ → ξ'`. The composite `R' → R → R'` of the inclusion with the base of `f` is then a
surjective endomorphism of the Noetherian ring `R'`, by the minimality clause of a smallest
descent, hence an isomorphism; and `f.base` followed by its inverse is the retraction.

## Main results

* `Deformation.exists_retraction_of_smallestDescent`: the inclusion of the smallest descended
  base admits a left inverse.
* `Deformation.exists_ideal_prodAddEquiv_of_smallestDescent`: the original base is the additive
  direct sum of the descended base and an ideal.

## Implementation notes

The levelwise lifting is organized by `Deformation.FormalLift`, which records a lift of one
level of a formal object through a morphism of categories over `𝒞_Λ`, and
`Deformation.FormalLiftStep`, which records the passage from one level to the next. The same
induction appears in the proof of Stacks 06HN
(`Deformation.completionMap_essSurj_of_isSmooth_of_fiber_essSurj`), where the lift at level
zero comes from essential surjectivity on the special fibre instead of from a descent; see the
report accompanying this file.

The ideal appearing in the additive decomposition is the kernel of the retraction, and the
equivalence is the one induced by the inclusion, so the decomposition is pinned down rather
than merely asserted to exist.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
* [Stacks Project, Tag 06T3](https://stacks.math.columbia.edu/tag/06T3)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w uF vF uG vG

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
variable {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A lift of level `n` of a formal object `η` of `q` through a morphism `φ` of categories
over `𝒞_Λ`: an object of the source lying over the `n`-th adic truncation of the base of `η`,
together with a vertical morphism from level `n` of `η` to its image. -/
public structure FormalLift
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (η : FormalObject q) (n : ℕ) where
  /-- The lifting object of the source category. -/
  obj : F
  /-- It lies over the `n`-th adic truncation of the base of `η`. -/
  obj_base : p.obj obj = (AdicTruncation.functor n).obj η.base
  /-- The comparison morphism from level `n` of `η`. -/
  app : η.level n ⟶ φ.obj obj
  /-- The comparison morphism is vertical. -/
  app_lift : q.IsHomLift (𝟙 ((AdicTruncation.functor n).obj η.base)) app

/-- The passage from a lift of level `n` of a formal object to a lift of level `n + 1`,
together with the transition morphism between the two lifting objects. -/
public structure FormalLiftStep
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (η : FormalObject q) (n : ℕ) (s : FormalLift φ η n) where
  /-- The lift one level up. -/
  next : FormalLift φ η (n + 1)
  /-- The transition morphism of the lifting objects. -/
  transition : next.obj ⟶ s.obj
  /-- It lies over the transition map of adic truncations. -/
  transition_lift : p.IsHomLift ((AdicTruncation.transitionNat n).app η.base) transition
  /-- The comparison morphisms are compatible with the transitions. -/
  naturality : η.transition n ≫ s.app = next.app ≫ φ.map transition

/-- A smooth morphism into a category cofibered in groupoids extends a lift of one level of a
formal object to a lift of the next level. -/
public lemma nonempty_formalLiftStep
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (hq : IsCofiberedInGroupoids q) (hφ : IsSmooth φ) (η : FormalObject q) (n : ℕ)
    (s : FormalLift φ η n) : Nonempty (FormalLiftStep φ η n s) := by
  let B := (AdicTruncation.functor (n + 1)).obj η.base
  let f := (AdicTruncation.transitionNat n).app η.base
  have hg : q.IsHomLift f (η.transition n ≫ s.app) := by
    have := η.transition_lift n
    have := s.app_lift
    exact IsHomLift.comp_lift_id_right q ((AdicTruncation.transitionNat n).app η.base)
      (η.transition n) s.app
  have hf : Function.Surjective f.hom := by
    dsimp only [f, AdicTruncation.transitionNat, AdicTruncation.transition]
    exact Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  obtain ⟨x, h, a, hh, ha, hcomm⟩ := hφ f hf (η.level (n + 1)) s.obj
    (η.transition n ≫ s.app) hg
  have : p.IsHomLift f h := hh
  have hx : p.obj x = B := IsHomLift.domain_eq (p := p) f h
  let i : φ.obj x ≅ η.level (n + 1) := isoOfIsHomLiftId hq a ha
  have hainv : q.IsHomLift (𝟙 B) i.inv := by
    have : q.IsHomLift (𝟙 B) i.hom := ha
    exact IsHomLift.lift_id_inv q B i
  refine ⟨⟨⟨x, hx, i.inv, hainv⟩, h, hh, ?_⟩⟩
  calc
    η.transition n ≫ s.app = i.inv ≫ (i.hom ≫ (η.transition n ≫ s.app)) := by
      rw [← Category.assoc, i.inv_hom_id, Category.id_comp]
    _ = i.inv ≫ φ.map h := by rw [hcomm, ← (show i.hom = a from rfl)]

/-- Each level of the image of a formal object under the completion of a based functor lies
over the corresponding adic truncation of the base of that image. -/
private theorem completionMap_obj_level_eq
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (X : FormalObject p) (n : ℕ) :
    q.obj (((completionMap φ).obj X).level n) =
      (AdicTruncation.functor n).obj ((completionMap φ).obj X).base := by
  have hw : q.obj (φ.obj (X.level n)) = p.obj (X.level n) := φ.w_obj (X.level n)
  rw [completionMap_obj_level φ X n, hw, X.level_eq n, completionMap_obj_base φ X]

/-- A smooth morphism into a category cofibered in groupoids lifts a formal object as soon as
its level zero lifts: the levelwise lifts assemble into a formal object of the source whose
image is isomorphic to the given formal object, over the identity of its base. -/
public theorem exists_formalObject_isoCompletionMap
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (hq : IsCofiberedInGroupoids q) (hφ : IsSmooth φ) (η : FormalObject q)
    (s₀ : FormalLift φ η 0) :
    ∃ X : FormalObject p, Nonempty (η ≅ (completionMap φ).obj X) := by
  classical
  let stepData (n : ℕ) (s : FormalLift φ η n) : FormalLiftStep φ η n s :=
    Classical.choice (nonempty_formalLiftStep φ hq hφ η n s)
  let states : (n : ℕ) → FormalLift φ η n :=
    Nat.rec s₀ (fun n s => (stepData n s).next)
  let X : FormalObject p :=
    { base := η.base
      level := fun n => (states n).obj
      level_eq := fun n => (states n).obj_base
      transition := fun n => (stepData n (states n)).transition
      transition_lift := fun n => (stepData n (states n)).transition_lift }
  have hcb : ((completionMap φ).obj X).base = η.base := by
    simp [completionMap_obj_base, X]
  let appMap (n : ℕ) := (states n).app ≫ eqToHom (completionMap_obj_level φ X n).symm
  let baseMap := eqToHom hcb.symm
  let m : η ⟶ (completionMap φ).obj X :=
    { base := baseMap
      app := appMap
      app_lift := fun n => by
        have hA : q.obj (η.level n) = (AdicTruncation.functor n).obj η.base := η.level_eq n
        have hB := completionMap_obj_level_eq φ X n
        have : q.IsHomLift (𝟙 ((AdicTruncation.functor n).obj η.base))
            (states n).app := (states n).app_lift
        have happfac := IsHomLift.fac' q
          (𝟙 ((AdicTruncation.functor n).obj η.base)) (states n).app
        have hmapcomp := q.map_comp (states n).app
          (eqToHom (completionMap_obj_level φ X n).symm)
        refine IsHomLift.of_fac q ((AdicTruncation.functor n).map baseMap)
          (appMap n) hA hB ?_
        show (AdicTruncation.functor n).map baseMap =
          eqToHom hA.symm ≫ q.map (appMap n) ≫ eqToHom hB
        dsimp only [appMap]
        calc
          _ = eqToHom (congrArg (fun R => (AdicTruncation.functor n).obj R) hcb.symm) := by
            dsimp only [baseMap]
            rw [eqToHom_map]
          _ = eqToHom hA.symm ≫ q.map ((states n).app ≫
                eqToHom (completionMap_obj_level φ X n).symm) ≫ eqToHom hB := by
            have hcomp := congrArg (fun g => eqToHom hA.symm ≫ g ≫ eqToHom hB) hmapcomp
            rw [happfac] at hcomp
            simpa [hA, hB, hcb, completionMap_obj_level, completionMap_obj_base, X,
              Category.assoc, eqToHom_trans_assoc, eqToHom_map] using hcomp.symm
      naturality := fun n => by
        have hn := congrArg (fun t => t ≫ eqToHom (completionMap_obj_level φ X n).symm)
          (stepData n (states n)).naturality
        simpa [appMap, completionMap_obj_transition, completionMap_obj_level,
          Category.assoc] using hn }
  let π := FormalObject.projection (p := q)
  have hπ : IsCofiberedInGroupoids π := formalObjectProjection_isCofiberedInGroupoids q hq
  have hm : π.IsHomLift (𝟙 η.base) m := by
    refine IsHomLift.of_fac π (𝟙 η.base) m rfl hcb ?_
    simp [π, m, baseMap, FormalObject.projection]
  exact ⟨X, ⟨isoOfIsHomLiftId hπ m hm⟩⟩

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The maximal ideal of the zeroth adic truncation of a complete local algebra vanishes: that
truncation is the residue field. -/
public theorem adicTruncation_zero_maximalIdeal_eq_bot
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    maximalIdeal (AdicTruncation.obj R 0) = ⊥ := by
  have h := adicTruncation_maximalIdeal_pow R 0
  rwa [Nat.zero_add, pow_one] at h

/-- The zeroth adic truncation of a morphism of complete local algebras is bijective: both
sides are the residue field, and the morphism respects the chosen identifications. -/
public theorem bijective_adicTruncation_map_zero
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    Function.Bijective (AdicTruncation.map f 0).hom := by
  have hfield (T : CompleteLocalAlgCat.{u, v, w} Λ k) : IsField (AdicTruncation.obj T 0) :=
    (isField_iff_maximalIdeal_eq).mpr (adicTruncation_zero_maximalIdeal_eq_bot T)
  let _ : Field (AdicTruncation.obj R 0) := (hfield R).toField
  let _ : Field (AdicTruncation.obj S 0) := (hfield S).toField
  refine ⟨RingHom.injective (AdicTruncation.map f 0).hom.toRingHom, fun y => ?_⟩
  obtain ⟨x, hx⟩ := residue_surjective
    ((AdicTruncation.obj R 0).residueEquiv.symm
      ((AdicTruncation.obj S 0).residueEquiv (residue (AdicTruncation.obj S 0) y)))
  refine ⟨x, ?_⟩
  have hres : residue (AdicTruncation.obj S 0) ((AdicTruncation.map f 0).hom x) =
      residue (AdicTruncation.obj S 0) y := by
    refine (AdicTruncation.obj S 0).residueEquiv.injective ?_
    calc
      (AdicTruncation.obj S 0).residueEquiv
          (residue (AdicTruncation.obj S 0) ((AdicTruncation.map f 0).hom x)) =
          (AdicTruncation.obj R 0).residueEquiv (residue (AdicTruncation.obj R 0) x) :=
        (AdicTruncation.map f 0).residue_comm x
      _ = (AdicTruncation.obj S 0).residueEquiv (residue (AdicTruncation.obj S 0) y) := by
        rw [hx]
        exact (AdicTruncation.obj R 0).residueEquiv.apply_symm_apply _
  have hmem := Ideal.Quotient.eq.mp hres
  rw [maximalIdeal_eq_bot] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

/-- The zeroth adic truncation of a morphism of complete local algebras is an isomorphism. -/
public theorem isIso_adicTruncation_map_zero
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    IsIso (AdicTruncation.map f 0) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ (bijective_adicTruncation_map_zero f)

/-- The quotient map onto an adic truncation, read through an equality of levels. -/
private theorem adicTruncation_cast_mk
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (h : n = m) (r : R) :
    (eqToHom (congrArg (AdicTruncation.obj R) h)).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal R m) r := by
  cases h
  rfl

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A morphism lying over an identity after precomposition with an identity-lifting morphism
lies over the corresponding equality of base objects. -/
private lemma isHomLift_eqToHom_of_isHomLift_id
    {C : Type*} [Category C] {D : Type*} [Category D] (r : D ⥤ C)
    {R S : C} (h : R = S) {a b : D} (f : a ⟶ b)
    (ha : r.obj a = R) (hb : r.obj b = S)
    (hf : r.IsHomLift (𝟙 S) f) : r.IsHomLift (eqToHom h) f := by
  refine IsHomLift.of_fac' r (eqToHom h) f ha hb ?_
  have hfac := IsHomLift.fac' r (𝟙 S) f
  have hd : IsHomLift.domain_eq r (𝟙 S) f = ha.trans h := Subsingleton.elim _ _
  have hc : IsHomLift.codomain_eq r (𝟙 S) f = hb := Subsingleton.elim _ _
  rw [hd, hc] at hfac
  simpa only [eqToHom_trans, Category.id_comp] using hfac

/-- The factorisation of an Artinian point at level zero inverts a given identification of the
point's underlying algebra with the zeroth adic truncation of the base of the versal formal
object. -/
private theorem comp_factor_eq_id
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (P : ChosenPushforwards p)
    (α : (restrictedCoyoneda ξ.base).Elements)
    (hlevel : (associatedMorphism hp ξ P).level α = 0)
    (g : α.1 ⟶ AdicTruncation.obj ξ.base 0) [IsIso g]
    (hg : ∀ x : ξ.base,
      (inv g).hom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0) x) = α.2.hom x) :
    (g ≫ eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm)) ≫
        (associatedMorphism hp ξ P).factor α = 𝟙 α.1 := by
  have hfactor : eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm) ≫
      (associatedMorphism hp ξ P).factor α = inv g := by
    refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    calc
      _ = ((associatedMorphism hp ξ P).factor α).hom
            ((eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm)).hom
              (Ideal.Quotient.mk _ x)) := rfl
      _ = ((associatedMorphism hp ξ P).factor α).hom (Ideal.Quotient.mk _ x) := by
        rw [adicTruncation_cast_mk ξ.base hlevel.symm x]
      _ = α.2.hom x := DFunLike.congr_fun ((associatedMorphism hp ξ P).factor_spec α).2.2 x
      _ = (inv g).hom (Ideal.Quotient.mk _ x) := (hg x).symm
  rw [Category.assoc, hfactor]
  exact IsIso.hom_inv_id g

/-- A morphism into level zero of a versal formal object whose base map is inverted by the
factorisation of an Artinian point becomes vertical after composition with the inclusion of
that point: this is the lifting condition of `Deformation.FormalLift` at level zero. -/
private theorem isHomLift_comp_pointInclusion
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (P : ChosenPushforwards p)
    (α : (restrictedCoyoneda ξ.base).Elements)
    (hlevel : (associatedMorphism hp ξ P).level α = 0)
    {Y : F} (φ : Y ⟶ ξ.level 0) (g : α.1 ⟶ AdicTruncation.obj ξ.base 0)
    (hφ : p.IsHomLift g φ)
    (hbase : (g ≫ eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm)) ≫
      (associatedMorphism hp ξ P).factor α = 𝟙 α.1) :
    p.IsHomLift (𝟙 α.1) (φ ≫ eqToHom (congrArg ξ.level hlevel.symm) ≫
      (associatedMorphism hp ξ P).pointInclusion α) := by
  have hpin : p.IsHomLift ((associatedMorphism hp ξ P).factor α)
      ((associatedMorphism hp ξ P).pointInclusion α) := by
    refine (IsHomLift.eqToHom_comp_lift_iff p ((associatedMorphism hp ξ P).factor α)
      ((associatedMorphism hp ξ P).pointInclusion α)
      ((associatedMorphism hp ξ P).obj_eq α)).mp ?_
    rw [(associatedMorphism hp ξ P).pointInclusion_eq]
    exact (P ((associatedMorphism hp ξ P).factor α)).cocartesian _ |>.toIsHomLift
  have hcast : p.IsHomLift (eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm))
      (eqToHom (congrArg ξ.level hlevel.symm)) :=
    isHomLift_eqToHom_of_isHomLift_id p
      (congrArg (AdicTruncation.obj ξ.base) hlevel.symm)
      (eqToHom (congrArg ξ.level hlevel.symm)) (ξ.level_eq 0)
      (ξ.level_eq ((associatedMorphism hp ξ P).level α))
      (IsHomLift.eqToHom_codomain_lift_id (congrArg ξ.level hlevel.symm)
        (ξ.level_eq ((associatedMorphism hp ξ P).level α)))
  have hc := IsHomLift.comp p
    (g ≫ eqToHom (congrArg (AdicTruncation.obj ξ.base) hlevel.symm))
    ((associatedMorphism hp ξ P).factor α)
    (φ ≫ eqToHom (congrArg ξ.level hlevel.symm))
    ((associatedMorphism hp ξ P).pointInclusion α)
  rw [hbase, Category.assoc] at hc
  exact hc

/-- The lift at level zero of the descended formal object supplied by a smallest descent: the
zeroth truncations of the two bases are identified by the inclusion, so the zeroth level of
the descended object maps into the value of the associated morphism of `ξ` at the resulting
Artinian point. -/
private noncomputable def formalLiftZeroOfSmallestDescent
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (P : ChosenPushforwards p)
    (d : SmallestDescent ξ) :
    FormalLift (associatedMorphism hp ξ P).toBasedFunctor d.object 0 := by
  classical
  let B := AdicTruncation.obj d.object.base 0
  let g : B ⟶ AdicTruncation.obj ξ.base 0 := AdicTruncation.map d.inclusion.base 0
  letI : IsIso g := isIso_adicTruncation_map_zero d.inclusion.base
  let α : (restrictedCoyoneda ξ.base).Elements :=
    ⟨B, quotientProjection ξ.base 0 ≫ artinianToComplete.map (inv g)⟩
  have hpow : maximalIdeal B ^ (0 + 1) = (⊥ : Ideal B) := by
    rw [Nat.zero_add, pow_one]
    exact adicTruncation_zero_maximalIdeal_eq_bot d.object.base
  have hlevel : (associatedMorphism hp ξ P).level α = 0 :=
    Nat.eq_zero_of_le_zero (((associatedMorphism hp ξ P).factor_spec α).2.1 0 hpow)
  refine ⟨α, rfl, d.inclusion.app 0 ≫ eqToHom (congrArg ξ.level hlevel.symm) ≫
    (associatedMorphism hp ξ P).pointInclusion α, ?_⟩
  exact isHomLift_comp_pointInclusion hp ξ P α hlevel (d.inclusion.app 0) g
    (d.inclusion.app_lift 0) (comp_factor_eq_id hp ξ P α hlevel g fun _ => rfl)

/-- A morphism from a formal object to the descended object of a smallest descent produces a
retraction of the descended base inclusion: composing the inclusion with the base map of the
morphism is a surjective, hence bijective, endomorphism of a Noetherian ring. -/
private theorem exists_retraction_of_hom_to_smallestDescent
    {ξ : FormalObject p} (d : SmallestDescent ξ) (f : ξ ⟶ d.object) :
    ∃ r : ξ.base ⟶ d.object.base, d.inclusion.base ≫ r = 𝟙 d.object.base := by
  let g : d.object.base ⟶ d.object.base := d.inclusion.base ≫ f.base
  have hg : Function.Surjective g.hom :=
    d.further_descent_surjective d.object (d.inclusion ≫ f)
  obtain ⟨e, he⟩ := surjective_endomorphism_noetherian_isomorphism d.object.base g.hom hg
  have hgInjective : Function.Injective g.hom := fun x y h =>
    e.injective (by rw [he x, he y]; exact h)
  let _ : IsIso g := CompleteLocalAlgCat.isIso_of_bijective_hom g ⟨hgInjective, hg⟩
  exact ⟨f.base ≫ inv g, by rw [← Category.assoc]; exact IsIso.hom_inv_id g⟩

/-- The inclusion of the base of a smallest descent of a versal formal object admits a left
inverse. -/
public theorem exists_retraction_of_smallestDescent
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (d : SmallestDescent ξ) :
    ∃ r : ξ.base ⟶ d.object.base, d.inclusion.base ≫ r = 𝟙 d.object.base := by
  classical
  let P := chosenPushforwardsOfCofibered p hp
  let φ := (associatedMorphism hp ξ P).toBasedFunctor
  obtain ⟨X, ⟨i⟩⟩ := exists_formalObject_isoCompletionMap φ hp (hξ P) d.object
    (formalLiftZeroOfSmallestDescent hp ξ P d)
  obtain ⟨g⟩ := nonempty_hom_completionMap_obj hp ξ P X
  exact exists_retraction_of_hom_to_smallestDescent d (g ≫ i.inv)

/-- The base of a versal formal object is the additive direct sum of the base of a smallest
descent of it and an ideal, the decomposition being the one induced by the inclusion. -/
public theorem exists_ideal_prodAddEquiv_of_smallestDescent
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (d : SmallestDescent ξ) :
    ∃ (I : Ideal ξ.base) (e : (d.object.base × I) ≃+ ξ.base),
      ∀ (a : d.object.base) (b : I),
        e (a, b) = d.inclusion.base.hom a + (b : ξ.base) := by
  obtain ⟨r, hr⟩ := exists_retraction_of_smallestDescent hp ξ hξ d
  let I : Ideal ξ.base := RingHom.ker r.hom.toRingHom
  let f : (d.object.base × I) →+ ξ.base :=
    { toFun := fun x => d.inclusion.base.hom x.1 + (x.2 : ξ.base)
      map_zero' := by simp
      map_add' := fun x y => by
        show d.inclusion.base.hom (x.1 + y.1) + ((x.2 + y.2 : I) : ξ.base) =
          (d.inclusion.base.hom x.1 + (x.2 : ξ.base)) +
            (d.inclusion.base.hom y.1 + (y.2 : ξ.base))
        rw [map_add, Submodule.coe_add]
        abel }
  have hsection (a : d.object.base) : r.hom (d.inclusion.base.hom a) = a := by
    simpa using congrArg (fun q : d.object.base ⟶ d.object.base => q.hom a) hr
  have hker (b : I) : r.hom (b : ξ.base) = 0 := RingHom.mem_ker.mp b.property
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      change d.inclusion.base.hom x.1 + (x.2 : ξ.base) =
        d.inclusion.base.hom y.1 + (y.2 : ξ.base) at hxy
      have hmap' : r.hom (d.inclusion.base.hom x.1) + r.hom (x.2 : ξ.base) =
          r.hom (d.inclusion.base.hom y.1) + r.hom (y.2 : ξ.base) := by
        simpa only [map_add] using congrArg r.hom hxy
      rw [hker x.2, hker y.2, hsection x.1, hsection y.1] at hmap'
      have hfst : x.1 = y.1 := by simpa using hmap'
      rw [hfst] at hxy
      exact Prod.ext hfst (Subtype.ext (add_left_cancel hxy))
    · intro z
      refine ⟨(r.hom z, ⟨z - d.inclusion.base.hom (r.hom z), ?_⟩), ?_⟩
      · refine RingHom.mem_ker.mpr ?_
        show r.hom (z - d.inclusion.base.hom (r.hom z)) = 0
        rw [map_sub, hsection, sub_self]
      · show d.inclusion.base.hom (r.hom z) + (z - d.inclusion.base.hom (r.hom z)) = z
        abel
  exact ⟨I, AddEquiv.ofBijective f hbij, fun _ _ => rfl⟩

end

end Deformation

end
