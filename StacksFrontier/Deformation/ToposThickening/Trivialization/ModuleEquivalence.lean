module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.TrivializedCategory
import StacksCore.Tactic.StacksAttribute

/-!
# Trivialized first order thickenings of a ringed topos are the `O`-modules

Stacks 08MG ends by asserting that the category of trivialized first order thickenings of a
ringed topos `(Sh(C), O)` is equivalent to the category of `O`-modules. This file proves it.

In one direction a sheaf of `O`-modules `M` goes to the square-zero extension `O ⊕ M`, with the
projection onto `O` as the structure map of the thickening and the inclusion of `O` as the
trivialization. That functor is fully faithful and essentially surjective: a morphism of split
square-zero extensions is determined by, and determines, an `O`-linear map on the module
summands, and a trivialized thickening `A` is recovered from its ideal `I` by the splitting
`O ⊕ I ≅ A` of the displayed equation of the remark, `(a, x) ↦ π♯(a) + x`.

## Main definitions

* `Deformation.ToposThickening.TrivializedThickening.sqZeroExt`: the trivialized first order
  thickening attached to a sheaf of `O`-modules.
* `Deformation.ToposThickening.TrivializedThickening.sqZeroExtFunctor`: the same, as a functor.
* `Deformation.ToposThickening.TrivializedThickening.idealIso`: a trivialized first order
  thickening is the square-zero extension of `O` by its own ideal.

## Main results

* `Deformation.ToposThickening.TrivializedThickening.isSheaf_sqZeroExt`: the square-zero
  extension of a sheaf of commutative rings on a site by a sheaf of modules is a sheaf.
* `Deformation.ToposThickening.TrivializedThickening.moduleEquivalence`: the category of
  trivialized first order thickenings of `(Sh(C), O)` is equivalent to the category of
  `O`-modules.

## Variance

**The Hom of `Deformation.ToposThickening.TrivializedThickening O` runs in the algebraic
direction**: an object is presented by its structure sheaf `A` on the site, and a morphism
`T ⟶ S` is a morphism `A_T ⟶ A_S` of *sheaves of commutative rings* commuting with the
surjections and the sections. That is the direction of `h^♯`, not of `h`: the source takes a
morphism of trivialized first order thickenings of `(Sh(C), O)` to be a morphism of ringed
topoi `h : (Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂)` with `π₂ ∘ h = π₁` (Stacks 08MK), whose `h^♯` goes
`O'₂ ⟶ O'₁` (Stacks 08MJ). So this category is the *opposite* of the source's, and the two
fields of `Hom` match the source's `h` with the roles of `T` and `S` exchanged.

The presentation is forced, not chosen for convenience: this repo has no category of ringed
topoi to take morphisms in, since `AlgebraicGeometry.RingedToposHom.comp` has no strict unit
and associativity laws (see
`StacksFrontier/Deformation/ToposThickening/Trivialization/RingedToposId.lean`). With the Hom in
this direction `M ↦ O ⊕ M` is *covariant*, and the equivalence is stated with no `ᵒᵖ` on the
module side.

### Relation to the ringed space form, Stacks 08L9

Stacks 08L9 is this same remark for ringed spaces, and
`AlgebraicGeometry.RingedSpaceThickening.trivializedThickeningEquivalence`, in
`StacksFrontier/Deformation/RingedSpaceThickening/TrivializedThickeningEquivalence.lean`, states
it *with* an `ᵒᵖ`:

    (SheafOfModules (ringSheaf X))ᵒᵖ ≌ TrivializedThickening X

**The two do not disagree.** There a trivialized thickening is a ringed space `X'` over `X` and
a morphism is a morphism `X'₁ ⟶ X'₂` of ringed spaces — the geometric direction, the source's
own (Stacks 08LD) — so `𝒢 ↦ (X, 𝒪_X ⋉ 𝒢)` is contravariant and the `ᵒᵖ` is mandatory there.
That category is the opposite of this one, and `Mod(𝒪)ᵒᵖ ≌ 𝒯` and `Mod(𝒪) ≌ 𝒯ᵒᵖ` are one
statement. Neither file may be read as licence to drop or add an `ᵒᵖ` in the other: the `ᵒᵖ`
tracks the Hom direction, and the Hom directions differ.

## Implementation notes

The equivalence is produced from fullness, faithfulness and essential surjectivity rather than
from an explicit quasi-inverse with unit and counit; the quasi-inverse is the ideal of
`StacksFrontier/Deformation/ToposThickening/Trivialization/TrivializedCategory.lean`, and
`idealIso` is the natural isomorphism it would be paired with.

`modPresheaf` and `modHom` are the identity on the underlying data. They exist because
`PresheafOfModules.sqZeroExtPresheaf` is stated for a presheaf of modules over `R ⋙ forget₂`
with `R` a presheaf of commutative rings, while a sheaf of `O`-modules presents its sheaf of
rings as `AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite O`; the two agree by
definition but not syntactically, and instance resolution for the action of `O` on a module
only fires for the former spelling.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ) — `h^♯` induces
  `ℐ₂ ⟶ ℐ₁`
* [Stacks Project, Tag 08MK](https://stacks.math.columbia.edu/tag/08MK) — what a morphism of
  trivialized first order thickenings is
* [Stacks Project, Tag 08L9](https://stacks.math.columbia.edu/tag/08L9) — the ringed space form
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules (sqZeroExtObj sqZeroExtMap sqZeroExtPresheaf sqZeroExtProj sqZeroExtInl
  sqZeroExtMk sqZeroExtFst sqZeroExtSnd sqZeroExt_ext)

universe u

namespace Deformation.ToposThickening.TrivializedThickening

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The square-zero extension of a sheaf of commutative rings on a site by a sheaf of modules
is a sheaf: a compatible family of pairs is a pair of compatible families. -/
theorem isSheaf_sqZeroExt {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (hR : Presheaf.IsSheaf J R) (hMs : Presheaf.IsSheaf J M.presheaf) :
    Presheaf.IsSheaf J (sqZeroExtPresheaf M) := by
  have hO : Presieve.IsSheaf J (R ⋙ CategoryTheory.forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type (J := J) _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (J := J) (P' := R)
        (CategoryTheory.forget CommRingCat)).mp hR)
  have hM : Presieve.IsSheaf J (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type (J := J) _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (J := J) (P' := M.presheaf)
        (CategoryTheory.forget AddCommGrpCat)).mp hMs)
  rw [Presheaf.isSheaf_iff_isSheaf_forget (J := J)
    (P' := sqZeroExtPresheaf M) (CategoryTheory.forget CommRingCat),
    isSheaf_iff_isSheaf_of_type]
  intro Y S hS x hx
  let xO : Presieve.FamilyOfElements (R ⋙ CategoryTheory.forget CommRingCat) S.arrows :=
    fun _ f hf => sqZeroExtFst (x f hf)
  let xM : Presieve.FamilyOfElements
      (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) S.arrows :=
    fun _ f hf => sqZeroExtSnd (x f hf)
  have hxO : xO.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ h =>
    congrArg sqZeroExtFst (hx g₁ g₂ h₁ h₂ h)
  have hxM : xM.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ h =>
    congrArg sqZeroExtSnd (hx g₁ g₂ h₁ h₂ h)
  obtain ⟨r, hr, hur⟩ := hO S hS xO hxO
  obtain ⟨m, hm, hum⟩ := hM S hS xM hxM
  refine ⟨sqZeroExtMk r m, fun Z f hf => sqZeroExt_ext (hr f hf) (hm f hf), fun s hs => ?_⟩
  exact sqZeroExt_ext
    ((hur (sqZeroExtFst s) fun Z f hf => congrArg sqZeroExtFst (hs f hf)).trans
      (PresheafOfModules.sqZeroExtFst_mk r m).symm)
    ((hum (sqZeroExtSnd s) fun Z f hf => congrArg sqZeroExtSnd (hs f hf)).trans
      (PresheafOfModules.sqZeroExtSnd_mk r m).symm)

/-- The underlying presheaf of modules of a sheaf of `O`-modules, with its sheaf of rings
spelled as the presheaf underlying `O`. This is the spelling in which the square-zero
extension construction applies. -/
abbrev modPresheaf (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PresheafOfModules.{u} (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := M.val

/-- A morphism of sheaves of `O`-modules, in the spelling of `modPresheaf`. -/
abbrev modHom {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (φ : M ⟶ N) :
    modPresheaf M ⟶ modPresheaf N := φ.val

/-- The trivialized first order thickening of `(Sh(C), O)` attached to a sheaf of `O`-modules
`M`: the square-zero extension `O ⊕ M`, with the projection and the inclusion of `O`. -/
noncomputable def sqZeroExt (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    TrivializedThickening O where
  A := ⟨sqZeroExtPresheaf (modPresheaf M),
    isSheaf_sqZeroExt (modPresheaf M) O.property M.isSheaf⟩
  proj := ⟨sqZeroExtProj (modPresheaf M)⟩
  split := ⟨sqZeroExtInl (modPresheaf M)⟩
  split_proj := by
    apply InducedCategory.hom_ext
    ext U a
    rfl
  sq_zero U x y hx hy := by
    have hx' : sqZeroExtFst x = 0 := hx
    have hy' : sqZeroExtFst y = 0 := hy
    refine sqZeroExt_ext ?_ ?_
    · change sqZeroExtFst x * sqZeroExtFst y = (0 : O.obj.obj U)
      rw [hx', zero_mul]
    · change sqZeroExtFst x • sqZeroExtSnd y + sqZeroExtFst y • sqZeroExtSnd x =
        (0 : (modPresheaf M).obj U)
      rw [hx', hy', zero_smul, zero_smul, add_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The structure sheaf of `sqZeroExt M` has the square-zero extension `O ⊕ M` as its
underlying presheaf. -/
@[simp]
theorem sqZeroExt_A_obj (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (sqZeroExt M).A.obj = sqZeroExtPresheaf (modPresheaf M) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The structure map of `sqZeroExt M` takes a local section of `O ⊕ M` to its
`O`-component. -/
@[simp]
theorem sqZeroExt_proj_apply (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : Cᵒᵖ) (z : sqZeroExtObj (modPresheaf M) U) :
    ((sqZeroExt M).proj.hom.app U).hom z = sqZeroExtFst z := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The trivialization of `sqZeroExt M` takes a local section `a` of `O` to `(a, 0)`. -/
@[simp]
theorem sqZeroExt_split_apply (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : Cᵒᵖ) (a : O.obj.obj U) :
    ((sqZeroExt M).split.hom.app U).hom a = sqZeroExtMk a 0 := rfl

variable {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- The morphism of square-zero extensions induced by a morphism of sheaves of modules. -/
noncomputable def sqZeroExtHom (φ : M ⟶ N) :
    sqZeroExtPresheaf (modPresheaf M) ⟶ sqZeroExtPresheaf (modPresheaf N) where
  app U := PresheafOfModules.sqZeroExtLift (modPresheaf N)
    ((sqZeroExtProj (modPresheaf M)).app U)
    ((AddMonoidHom.mk'
      (fun z : sqZeroExtObj (modPresheaf M) U => ((modHom φ).app U).hom (sqZeroExtSnd z))
      fun z w => map_add ((modHom φ).app U).hom (sqZeroExtSnd z) (sqZeroExtSnd w) :
        sqZeroExtObj (modPresheaf M) U →+ (modPresheaf N).obj U))
    (fun z w => by
      have h := congrArg ((modHom φ).app U).hom (PresheafOfModules.sqZeroExtSnd_mul z w)
      rw [map_add, map_smul, map_smul] at h
      exact h)
  naturality U V f := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => sqZeroExt_ext rfl ?_)
    change ((modHom φ).app V).hom
        (sqZeroExtSnd ((sqZeroExtMap (modPresheaf M) f).hom z)) =
      (modPresheaf N).map f (((modHom φ).app U).hom (sqZeroExtSnd z))
    exact (congrArg ((modHom φ).app V).hom
        (PresheafOfModules.sqZeroExtSnd_map (M := modPresheaf M) f z)).trans
      (PresheafOfModules.naturality_apply (modHom φ) f (sqZeroExtSnd z))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `sqZeroExtHom φ` preserves the `O`-component of a local section. -/
@[simp]
theorem sqZeroExtHom_fst (φ : M ⟶ N) (U : Cᵒᵖ) (z : sqZeroExtObj (modPresheaf M) U) :
    sqZeroExtFst (((sqZeroExtHom φ).app U).hom z) = sqZeroExtFst z := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `sqZeroExtHom φ` acts on the module component of a local section by `φ`. -/
@[simp]
theorem sqZeroExtHom_snd (φ : M ⟶ N) (U : Cᵒᵖ) (z : sqZeroExtObj (modPresheaf M) U) :
    sqZeroExtSnd (((sqZeroExtHom φ).app U).hom z) = ((modHom φ).app U).hom (sqZeroExtSnd z) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Every local section of a square-zero extension is the sum of a section of the base and a
section of the module. -/
theorem sqZeroExt_decomp (U : Cᵒᵖ) (z : sqZeroExtObj (modPresheaf M) U) :
    z = sqZeroExtMk (sqZeroExtFst z) 0 + sqZeroExtMk (0 : O.obj.obj U) (sqZeroExtSnd z) :=
  sqZeroExt_ext (by simp) (by simp)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Multiplying a section of the module by a section of the base is the module action. -/
theorem sqZeroExtMk_mul (U : Cᵒᵖ) (a : O.obj.obj U) (m : (modPresheaf M).obj U) :
    sqZeroExtMk (M := modPresheaf M) a 0 * sqZeroExtMk (0 : O.obj.obj U) m =
      sqZeroExtMk (0 : O.obj.obj U) (a • m) :=
  sqZeroExt_ext (by simp) (by simp)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Restriction carries a section of the module to a section of the module. -/
theorem sqZeroExtMap_mk_zero {U V : Cᵒᵖ} (f : U ⟶ V) (m : (modPresheaf M).obj U) :
    (sqZeroExtMap (modPresheaf M) f).hom (sqZeroExtMk (0 : O.obj.obj U) m) =
      sqZeroExtMk (0 : O.obj.obj V) ((modPresheaf M).map f m) :=
  sqZeroExt_ext (map_zero (O.obj.map f).hom) rfl

/-- The functor from sheaves of `O`-modules to trivialized first order thickenings of
`(Sh(C), O)`. -/
noncomputable def sqZeroExtFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤ TrivializedThickening O where
  obj M := sqZeroExt M
  map {M N} φ :=
    { hom := ⟨sqZeroExtHom φ⟩
      hom_proj := by
        apply InducedCategory.hom_ext
        ext U z
        rfl
      split_hom := by
        apply InducedCategory.hom_ext
        ext U a
        exact sqZeroExt_ext rfl (map_zero ((modHom φ).app U).hom) }
  map_id M := by
    refine hom_ext (InducedCategory.hom_ext ?_)
    ext U z
    rfl
  map_comp φ ψ := by
    refine hom_ext (InducedCategory.hom_ext ?_)
    ext U z
    rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- On local sections, `sqZeroExtFunctor.map φ` takes `(a, m)` to `(a, φ m)`. -/
@[simp]
theorem sqZeroExtFunctor_map_apply (φ : M ⟶ N) (U : Cᵒᵖ)
    (z : sqZeroExtObj (modPresheaf M) U) :
    ((sqZeroExtFunctor.map φ).hom.hom.app U).hom z =
      sqZeroExtMk (sqZeroExtFst z) (((modHom φ).app U).hom (sqZeroExtSnd z)) := rfl

section Faithful

/-- The functor `M ↦ O ⊕ M` is faithful: a morphism of sheaves of modules is recovered from its
action on the module summand. -/
instance : (sqZeroExtFunctor (O := O)).Faithful where
  map_injective {M N} φ ψ h := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    exact congrArg (fun g : sqZeroExt M ⟶ sqZeroExt N =>
      sqZeroExtSnd ((g.hom.hom.app U).hom (sqZeroExtMk (0 : O.obj.obj U) m))) h

end Faithful

section Full

variable (f : sqZeroExt M ⟶ sqZeroExt N)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism of split square-zero extensions preserves the projection to `O`. -/
theorem fst_apply_of_hom (U : Cᵒᵖ) (z : sqZeroExtObj (modPresheaf M) U) :
    sqZeroExtFst ((f.hom.hom.app U).hom z) = sqZeroExtFst z :=
  congrArg (fun g : (sqZeroExt M).A ⟶ O => (g.hom.app U).hom z) f.hom_proj

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism of split square-zero extensions preserves the inclusion of `O`. -/
theorem apply_mk_zero_of_hom (U : Cᵒᵖ) (a : O.obj.obj U) :
    (f.hom.hom.app U).hom (sqZeroExtMk a 0) = sqZeroExtMk a 0 :=
  congrArg (fun g : O ⟶ (sqZeroExt N).A => (g.hom.app U).hom a) f.split_hom

/-- The map of modules underlying a morphism of split square-zero extensions. -/
noncomputable def ofHomFun (U : Cᵒᵖ) (m : (modPresheaf M).obj U) : (modPresheaf N).obj U :=
  sqZeroExtSnd ((f.hom.hom.app U).hom (sqZeroExtMk (0 : O.obj.obj U) m))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism of split square-zero extensions takes a section `(0, m)` of the module summand
to `(0, ofHomFun f U m)`. -/
theorem apply_mk_zero (U : Cᵒᵖ) (m : (modPresheaf M).obj U) :
    (f.hom.hom.app U).hom (sqZeroExtMk (0 : O.obj.obj U) m) =
      sqZeroExtMk (0 : O.obj.obj U) (ofHomFun f U m) :=
  sqZeroExt_ext (fst_apply_of_hom f U _) rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `ofHomFun f U` is additive. -/
theorem ofHomFun_add (U : Cᵒᵖ) (m m' : (modPresheaf M).obj U) :
    ofHomFun f U (m + m') = ofHomFun f U m + ofHomFun f U m' := by
  have hmk : sqZeroExtMk (M := modPresheaf M) (0 : O.obj.obj U) (m + m') =
      sqZeroExtMk (0 : O.obj.obj U) m + sqZeroExtMk (0 : O.obj.obj U) m' :=
    sqZeroExt_ext (add_zero (0 : O.obj.obj U)).symm rfl
  exact congrArg sqZeroExtSnd
    ((congrArg (f.hom.hom.app U).hom hmk).trans (map_add (f.hom.hom.app U).hom _ _))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `ofHomFun f U` is `O`-linear. -/
theorem ofHomFun_smul (U : Cᵒᵖ) (a : O.obj.obj U) (m : (modPresheaf M).obj U) :
    ofHomFun f U (a • m) = a • ofHomFun f U m := by
  have e1 : (f.hom.hom.app U).hom (sqZeroExtMk (0 : O.obj.obj U) (a • m)) =
      (f.hom.hom.app U).hom (sqZeroExtMk a 0 * sqZeroExtMk (0 : O.obj.obj U) m) :=
    congrArg (f.hom.hom.app U).hom (sqZeroExtMk_mul U a m).symm
  have e2 : (f.hom.hom.app U).hom (sqZeroExtMk a 0 * sqZeroExtMk (0 : O.obj.obj U) m) =
      sqZeroExtMk a 0 * sqZeroExtMk (0 : O.obj.obj U) (ofHomFun f U m) :=
    (map_mul (f.hom.hom.app U).hom _ _).trans
      (congrArg₂ (· * ·) (apply_mk_zero_of_hom f U a) (apply_mk_zero f U m))
  exact congrArg sqZeroExtSnd
    (e1.trans (e2.trans (sqZeroExtMk_mul (M := N) U a (ofHomFun f U m))))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `ofHomFun f` commutes with the restriction maps of the two modules. -/
theorem ofHomFun_naturality {U V : Cᵒᵖ} (g : U ⟶ V) (m : (modPresheaf M).obj U) :
    ofHomFun f V ((modPresheaf M).map g m) = (modPresheaf N).map g (ofHomFun f U m) := by
  have hnat := congrArg
    (fun h : (sqZeroExt M).A.obj.obj U ⟶ (sqZeroExt N).A.obj.obj V =>
      h.hom (sqZeroExtMk (0 : O.obj.obj U) m)) (f.hom.hom.naturality g)
  have hL : (f.hom.hom.app V).hom
      ((sqZeroExtMap (modPresheaf M) g).hom (sqZeroExtMk (0 : O.obj.obj U) m)) =
      sqZeroExtMk (0 : O.obj.obj V) (ofHomFun f V ((modPresheaf M).map g m)) :=
    (congrArg (f.hom.hom.app V).hom (sqZeroExtMap_mk_zero g m)).trans
      (apply_mk_zero f V ((modPresheaf M).map g m))
  have hR : (sqZeroExtMap (modPresheaf N) g).hom
      ((f.hom.hom.app U).hom (sqZeroExtMk (0 : O.obj.obj U) m)) =
      sqZeroExtMk (0 : O.obj.obj V) ((modPresheaf N).map g (ofHomFun f U m)) :=
    (congrArg (sqZeroExtMap (modPresheaf N) g).hom (apply_mk_zero f U m)).trans
      (sqZeroExtMap_mk_zero g (ofHomFun f U m))
  exact congrArg sqZeroExtSnd (hL.symm.trans (hnat.trans hR))

/-- The morphism of sheaves of modules underlying a morphism of split square-zero
extensions. -/
noncomputable def ofHom : M ⟶ N :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := ofHomFun f U
        map_add' := ofHomFun_add f U
        map_smul' := fun a m => ofHomFun_smul f U a m }
     naturality := fun {_U _V} g =>
       ModuleCat.hom_ext (LinearMap.ext fun m => ofHomFun_naturality f g m) }⟩

/-- The functor `M ↦ O ⊕ M` is full: a morphism `f` of split square-zero extensions is the
image of the morphism of modules `ofHom f`. -/
instance : (sqZeroExtFunctor (O := O)).Full where
  map_surjective {M N} f := by
    refine ⟨ofHom f, hom_ext (InducedCategory.hom_ext (NatTrans.ext (funext fun U => ?_)))⟩
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    change sqZeroExtMk (sqZeroExtFst z) (ofHomFun f U (sqZeroExtSnd z)) =
      (f.hom.hom.app U).hom z
    have hdec : (f.hom.hom.app U).hom z =
        sqZeroExtMk (sqZeroExtFst z) 0 +
          sqZeroExtMk (0 : O.obj.obj U) (ofHomFun f U (sqZeroExtSnd z)) :=
      (congrArg (f.hom.hom.app U).hom (sqZeroExt_decomp U z)).trans
        ((map_add (f.hom.hom.app U).hom _ _).trans
          (congrArg₂ (· + ·) (apply_mk_zero_of_hom f U (sqZeroExtFst z))
            (apply_mk_zero f U (sqZeroExtSnd z))))
    exact (sqZeroExt_ext (add_zero _).symm (zero_add _).symm).trans hdec.symm

end Full

section EssSurj

variable (T : TrivializedThickening O)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The surjection kills a local section of the ideal. -/
theorem proj_ideal_val {U : Cᵒᵖ} (x : (modPresheaf T.ideal).obj U) :
    (T.proj.hom.app U).hom x.1 = 0 := T.mem_idealSections.mp x.2

/-- The section of the ideal cut out by subtracting the trivialization of the image. -/
noncomputable def idealOfSection {U : Cᵒᵖ} (x : T.A.obj.obj U) : T.idealSections U :=
  ⟨x - (T.split.hom.app U).hom ((T.proj.hom.app U).hom x), by
    rw [T.mem_idealSections, map_sub, T.proj_split_apply, sub_self]⟩

/-- The identification of the square-zero extension `O ⊕ I` with the structure sheaf of a
trivialized thickening, on local sections: `(a, x) ↦ π♯(a) + x`. -/
noncomputable def idealEquiv (U : Cᵒᵖ) :
    sqZeroExtObj (modPresheaf T.ideal) U ≃+* T.A.obj.obj U where
  toFun z := (T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1
  invFun x := sqZeroExtMk ((T.proj.hom.app U).hom x) (T.idealOfSection x)
  left_inv z := by
    have h1 : (T.proj.hom.app U).hom
        ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1) =
          sqZeroExtFst z := by
      rw [map_add, T.proj_split_apply, T.proj_ideal_val, add_zero]
    refine sqZeroExt_ext h1 (Subtype.ext ?_)
    change (T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1 -
        (T.split.hom.app U).hom ((T.proj.hom.app U).hom
          ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1)) =
      (sqZeroExtSnd z).1
    rw [h1]
    ring
  right_inv x := by
    change (T.split.hom.app U).hom ((T.proj.hom.app U).hom x) +
      (x - (T.split.hom.app U).hom ((T.proj.hom.app U).hom x)) = x
    ring
  map_mul' z w := by
    have h0 := T.sq_zero U (sqZeroExtSnd z).1 (sqZeroExtSnd w).1
      (T.proj_ideal_val (sqZeroExtSnd z)) (T.proj_ideal_val (sqZeroExtSnd w))
    change (T.split.hom.app U).hom (sqZeroExtFst z * sqZeroExtFst w) +
        ((T.split.hom.app U).hom (sqZeroExtFst z) * (sqZeroExtSnd w).1 +
          (T.split.hom.app U).hom (sqZeroExtFst w) * (sqZeroExtSnd z).1) =
      ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1) *
        ((T.split.hom.app U).hom (sqZeroExtFst w) + (sqZeroExtSnd w).1)
    have hexp : ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1) *
        ((T.split.hom.app U).hom (sqZeroExtFst w) + (sqZeroExtSnd w).1) =
        (T.split.hom.app U).hom (sqZeroExtFst z) * (T.split.hom.app U).hom (sqZeroExtFst w) +
          ((T.split.hom.app U).hom (sqZeroExtFst z) * (sqZeroExtSnd w).1 +
            (T.split.hom.app U).hom (sqZeroExtFst w) * (sqZeroExtSnd z).1) +
          (sqZeroExtSnd z).1 * (sqZeroExtSnd w).1 := by ring
    rw [map_mul, hexp, h0, add_zero]
  map_add' z w := by
    change (T.split.hom.app U).hom (sqZeroExtFst z + sqZeroExtFst w) +
        ((sqZeroExtSnd z).1 + (sqZeroExtSnd w).1) =
      ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1) +
        ((T.split.hom.app U).hom (sqZeroExtFst w) + (sqZeroExtSnd w).1)
    rw [map_add]
    ring

/-- The identification `O ⊕ I ≅ A` as presheaves of commutative rings. -/
noncomputable def idealPresheafIso :
    sqZeroExtPresheaf (modPresheaf T.ideal) ≅ T.A.obj :=
  NatIso.ofComponents (fun U => (T.idealEquiv U).toCommRingCatIso) (by
    intro U V f
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    change (T.split.hom.app V).hom ((O.obj.map f).hom (sqZeroExtFst z)) +
        (T.A.obj.map f).hom (sqZeroExtSnd z).1 =
      (T.A.obj.map f).hom ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1)
    rw [map_add, T.split_naturality_apply])

/-- The identification `O ⊕ I ≅ A` as sheaves of commutative rings. -/
noncomputable def idealSheafIso : (sqZeroExt T.ideal).A ≅ T.A :=
  InducedCategory.isoMk T.idealPresheafIso

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The identification `O ⊕ I ≅ A` commutes with the structure maps to `O`. -/
theorem idealSheafIso_proj : T.idealSheafIso.hom ≫ T.proj = (sqZeroExt T.ideal).proj := by
  apply InducedCategory.hom_ext
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun z => ?_))
  change (T.proj.hom.app U).hom
      ((T.split.hom.app U).hom (sqZeroExtFst z) + (sqZeroExtSnd z).1) = sqZeroExtFst z
  rw [map_add, T.proj_split_apply, T.proj_ideal_val, add_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The identification `O ⊕ I ≅ A` commutes with the trivializations. -/
theorem idealSheafIso_split : (sqZeroExt T.ideal).split ≫ T.idealSheafIso.hom = T.split := by
  apply InducedCategory.hom_ext
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  change (T.split.hom.app U).hom a + (0 : T.A.obj.obj U) = (T.split.hom.app U).hom a
  exact add_zero _

/-- A trivialized first order thickening of `(Sh(C), O)` is the square-zero extension of `O`
by its ideal. -/
noncomputable def idealIso : sqZeroExt T.ideal ≅ T where
  hom := ⟨T.idealSheafIso.hom, T.idealSheafIso_proj, T.idealSheafIso_split⟩
  inv := ⟨T.idealSheafIso.inv, by
      rw [← T.idealSheafIso_proj, ← Category.assoc, Iso.inv_hom_id, Category.id_comp], by
      rw [← T.idealSheafIso_split, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := hom_ext T.idealSheafIso.hom_inv_id
  inv_hom_id := hom_ext T.idealSheafIso.inv_hom_id

/-- The functor `M ↦ O ⊕ M` is essentially surjective: a trivialized first order thickening is
the square-zero extension of `O` by its ideal, by `idealIso`. -/
instance : (sqZeroExtFunctor (O := O)).EssSurj where
  mem_essImage T := ⟨T.ideal, ⟨T.idealIso⟩⟩

end EssSurj

/-- The functor `M ↦ O ⊕ M` is an equivalence, being full, faithful and essentially
surjective. -/
instance : (sqZeroExtFunctor (O := O)).IsEquivalence where

variable (O)

/-- **Stacks 08MG.** The category of trivialized first order thickenings of a ringed topos
`(Sh(C), O)` is equivalent to the category of `O`-modules: a module goes to the square-zero
extension `O ⊕ M`, and a trivialized thickening goes to its ideal.

There is no `ᵒᵖ` on the module side because the Hom of
`Deformation.ToposThickening.TrivializedThickening O` runs in the algebraic direction, a
morphism `T ⟶ S` being a morphism `A_T ⟶ A_S` of sheaves of rings, so that this category is the
opposite of the source's category of trivialized thickenings (whose morphisms are morphisms of
ringed topoi, Stacks 08MK) and `M ↦ O ⊕ M` is covariant. The ringed space form of this remark,
`AlgebraicGeometry.RingedSpaceThickening.trivializedThickeningEquivalence` (**Stacks 08L9**),
keeps the geometric Hom and so *does* carry an `ᵒᵖ`; the two statements agree. See the
"## Variance" section of this module. -/
@[stacks 08MG "trivialized first order thickenings are the O-modules; morphisms of thickenings \
run in the algebraic direction (A_T ⟶ A_S of sheaves of rings, the opposite of the source's \
ringed-topos morphisms of Stacks 08MK), so the module side carries no ᵒᵖ; stated at a single \
universe (site C : Type u with Category.{u} C, sheaves valued in Type u), which is the source's \
own setting since the Stacks Project fixes one universe throughout"]
noncomputable def moduleEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ≌ TrivializedThickening O :=
  (sqZeroExtFunctor (O := O)).asEquivalence

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The functor of `moduleEquivalence O` is `sqZeroExtFunctor`. -/
@[simp]
theorem moduleEquivalence_functor :
    (moduleEquivalence O).functor = sqZeroExtFunctor := rfl

end Deformation.ToposThickening.TrivializedThickening

end
