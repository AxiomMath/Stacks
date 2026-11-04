module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extensions of a sheaf of rings by a sheaf of abelian groups, over a base sheaf of rings

Let `(C, K)` be a site, let `𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on it and let
`𝒢` be a presheaf of abelian groups.  An *extension of `ℬ` by `𝒢` over `𝒜`* is a sheaf of
commutative rings `𝒪` together with

* a morphism `𝒜 ⟶ 𝒪` of sheaves of rings and a locally surjective morphism `𝒪 ⟶ ℬ` whose
  composite is the given `𝒜 ⟶ ℬ`, and
* a natural, injective, additive family `𝒢(U) ⟶ 𝒪(U)` whose image is *exactly* the kernel of
  `𝒪(U) ⟶ ℬ(U)`, and which squares to zero.

This is the notion the remark **Stacks 0GQ2** compares its two constructions in: `𝒪'₁` and
`𝒪'₂` are extensions of `g⁻¹𝒪_X` by `𝒢` over `g⁻¹f⁻¹𝒪_S`, and the remark's criterion is that
they are isomorphic as such.  Neither
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution` nor
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom` applies: those are about the structure
sheaf of a ringed space, and `g⁻¹𝒪_X` is not one.

## Main definitions

* `Stacks.Sites.SqZeroExtension.AlgebraExtension`: the extension, as above.
* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom`: a morphism of extensions — a morphism of
  the middle sheaves of rings which is a morphism of `𝒜`-algebras, lies over `ℬ`, and is the
  identity on `𝒢`.
* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Isomorphic`: the relation "isomorphic as
  extensions".  By `AlgebraExtension.Hom.isIso` any morphism of extensions is already an
  isomorphism, so this is an equivalence relation and not merely a preorder.
* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.symm`: the inverse of a morphism of
  extensions, built from the sectionwise inverse.

## Main results

* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.app_injective`,
  `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.app_surjective` and
  `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.app_bijective`: **the five lemma for
  extensions of sheaves of rings** — a morphism of extensions is bijective on sections.
* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.isIso`: hence an isomorphism.
* `Stacks.Sites.SqZeroExtension.AlgebraExtension.Isomorphic.refl`,
  `Stacks.Sites.SqZeroExtension.AlgebraExtension.Isomorphic.symm` and
  `Stacks.Sites.SqZeroExtension.AlgebraExtension.Isomorphic.trans`.

## Implementation notes

**Why the ideal is sectionwise data and not a sheaf of modules.**  The two extensions of
**Stacks 0GQ2** present their ideal in incompatible ways: the pushout's is the image of
`n ↦ [(0, n)]` through a *sheafification*, and the pullback's is the inclusion `n ↦ (ι n, 0)`
into a fibre product.  What both have, and all that any statement below needs, is the
sectionwise additive family together with naturality, injectivity and the exact kernel
computation, so that is what `AlgebraExtension` records.  In particular no action of `ℬ` on `𝒢`
appears in the structure: the five lemma does not use one, and the one place an action is
needed — checking that a comparison map is multiplicative — belongs to the construction that
produces the comparison, not to this interface.

**Why the projection is only locally surjective.**  For the pushout of **Stacks 0GQ2** it is: a
section of `g⁻¹𝒪_X` lifts to the pushout only locally, which is the whole reason
`Stacks.Sites.SqZeroPushout.pushoutSheaf` is a sheafification.  Left exactness and the kernel
computation, by contrast, hold on the nose for both constructions, and the five lemma below
uses that: injectivity of a morphism of extensions needs no covering sieve at all, and only
surjectivity has to be glued.

**The five lemma.**  Injectivity is a three-line chase.  Surjectivity is local — a section of
`𝒪₂` is hit after restriction along a covering sieve — and is promoted to a global statement by
`AlgebraExtension.Hom.exists_app_eq_of_locally`, the same argument as
`Stacks.Sites.SqZeroPushout.exists_pushoutInr_of_locally`: the local preimages are unique by
injectivity, hence agree on overlaps, hence glue in `𝒪₁`, and the glued section has the right
image because `𝒪₂` is separated.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sites.SqZeroPushout (isSheaf_forgetCommRing eq_of_locally_eq)

universe u

namespace Stacks.Sites.SqZeroExtension

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  {A B : Sheaf K CommRingCat.{u}} {base : A ⟶ B} {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}

/-- An extension `0 ⟶ 𝒢 ⟶ 𝒪 ⟶ ℬ ⟶ 0` of the sheaf of commutative rings `ℬ` by the presheaf of
abelian groups `𝒢`, in the category of `𝒜`-algebras: the projection onto `ℬ` is locally
surjective, its kernel on sections is exactly the image of `𝒢`, and that image squares to
zero. -/
structure AlgebraExtension (A B : Sheaf K CommRingCat.{u}) (base : A ⟶ B)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  /-- The middle sheaf of commutative rings. -/
  O : Sheaf K CommRingCat.{u}
  /-- The structure morphism making `𝒪` an `𝒜`-algebra. -/
  fromBase : A ⟶ O
  /-- The projection onto `ℬ`. -/
  proj : O ⟶ B
  /-- The projection is a morphism of `𝒜`-algebras. -/
  fromBase_comp_proj : fromBase ≫ proj = base
  /-- The projection is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective K proj.hom
  /-- The inclusion of the ideal `𝒢`, on sections. -/
  inr (X : Cᵒᵖ) : ↥(G.obj X) →+ ↥(O.obj.obj X)
  /-- The inclusion commutes with the restriction maps. -/
  inr_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥(G.obj X)) :
    (O.obj.map f).hom (inr X n) = inr Y ((G.map f) n)
  /-- The inclusion is injective on sections. -/
  inr_injective (X : Cᵒᵖ) : Function.Injective (inr X)
  /-- The kernel of the projection on sections is exactly the image of `𝒢`. -/
  proj_app_eq_zero_iff (X : Cᵒᵖ) (s : ↥(O.obj.obj X)) :
    proj.hom.app X s = 0 ↔ ∃ n : ↥(G.obj X), inr X n = s
  /-- The ideal `𝒢` squares to zero. -/
  inr_mul_inr (X : Cᵒᵖ) (n m : ↥(G.obj X)) : inr X n * inr X m = 0

namespace AlgebraExtension

variable (E : AlgebraExtension A B base G)

attribute [instance] locallySurjective

/-- The projection of an extension kills the ideal `𝒢`. -/
theorem proj_inr (X : Cᵒᵖ) (n : ↥(G.obj X)) : E.proj.hom.app X (E.inr X n) = 0 :=
  (E.proj_app_eq_zero_iff X _).2 ⟨n, rfl⟩

/-- The structure morphism of an extension followed by the projection, on sections. -/
theorem proj_fromBase (X : Cᵒᵖ) (a : ↥(A.obj.obj X)) :
    E.proj.hom.app X (E.fromBase.hom.app X a) = base.hom.app X a :=
  congrArg (fun t : A ⟶ B => t.hom.app X a) E.fromBase_comp_proj

/-- A local section of an extension killed by the projection comes from `𝒢`. -/
theorem exists_inr_eq {X : Cᵒᵖ} {s : ↥(E.O.obj.obj X)} (hs : E.proj.hom.app X s = 0) :
    ∃ n : ↥(G.obj X), E.inr X n = s := (E.proj_app_eq_zero_iff X s).1 hs

/-! ### Morphisms of extensions -/

/-- A morphism of extensions of `ℬ` by `𝒢` over `𝒜`: a morphism of the middle sheaves of
commutative rings which is a morphism of `𝒜`-algebras, lies over `ℬ`, and restricts to the
identity on the ideal `𝒢`. -/
structure Hom (E₁ E₂ : AlgebraExtension A B base G) where
  /-- The morphism of the middle sheaves of rings. -/
  hom : E₁.O ⟶ E₂.O
  /-- It is a morphism of `𝒜`-algebras. -/
  base_comm : E₁.fromBase ≫ hom = E₂.fromBase
  /-- It lies over `ℬ`. -/
  proj_comm : hom ≫ E₂.proj = E₁.proj
  /-- It is the identity on the ideal `𝒢`. -/
  inr_comm (X : Cᵒᵖ) (n : ↥(G.obj X)) :
    hom.hom.app X (E₁.inr X n) = E₂.inr X n

namespace Hom

variable {E₁ E₂ E₃ : AlgebraExtension A B base G}

/-- A morphism of extensions lies over `ℬ`, on sections. -/
theorem proj_app (e : Hom E₁ E₂) (X : Cᵒᵖ) (s : ↥(E₁.O.obj.obj X)) :
    E₂.proj.hom.app X (e.hom.hom.app X s) = E₁.proj.hom.app X s :=
  congrArg (fun t : E₁.O ⟶ B => t.hom.app X s) e.proj_comm

/-- A morphism of extensions commutes with the restriction maps, on sections. -/
theorem app_map (e : Hom E₁ E₂) {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : ↥(E₁.O.obj.obj X)) :
    e.hom.hom.app Y ((E₁.O.obj.map f).hom s) = (E₂.O.obj.map f).hom (e.hom.hom.app X s) :=
  NatTrans.naturality_apply e.hom.hom f s

/-- **The five lemma, injectivity.**  A morphism of extensions is injective on sections: a
section in its kernel is killed by the projection of `𝒪₁`, hence comes from `𝒢`, and `𝒢` is
carried to `𝒢` injectively. -/
theorem app_injective (e : Hom E₁ E₂) (X : Cᵒᵖ) :
    Function.Injective (e.hom.hom.app X) := by
  intro s t hst
  have hzero : e.hom.hom.app X (s - t) = 0 := by
    rw [map_sub, hst, sub_self]
  have hproj : E₁.proj.hom.app X (s - t) = 0 := by
    rw [← e.proj_app X (s - t), hzero, map_zero]
  obtain ⟨n, hn⟩ := E₁.exists_inr_eq hproj
  have hn2 : E₂.inr X n = 0 := by
    rw [← e.inr_comm X n, hn, hzero]
  have hn0 : n = 0 := E₂.inr_injective X (hn2.trans (map_zero (E₂.inr X)).symm)
  rw [← sub_eq_zero, ← hn, hn0, map_zero]

/-- A morphism of extensions is locally surjective on sections: a local section of `𝒪₂` lifts
after restriction along a covering sieve, because the projection of `𝒪₁` does and the difference
of the two lifts is then a section of `𝒢`. -/
theorem exists_app_eq_locally (e : Hom E₁ E₂) {X : Cᵒᵖ} (s : ↥(E₂.O.obj.obj X))
    {Y : C} (f : Y ⟶ X.unop)
    (hf : Presheaf.imageSieve E₁.proj.hom (E₂.proj.hom.app X s) f) :
    ∃ t : ↥(E₁.O.obj.obj (op Y)),
      e.hom.hom.app (op Y) t = (E₂.O.obj.map f.op).hom s := by
  obtain ⟨r, hr⟩ := hf
  have hdiff : E₂.proj.hom.app (op Y)
      (e.hom.hom.app (op Y) r - (E₂.O.obj.map f.op).hom s) = 0 := by
    rw [map_sub, e.proj_app (op Y) r, hr, NatTrans.naturality_apply E₂.proj.hom f.op s, sub_self]
  obtain ⟨n, hn⟩ := E₂.exists_inr_eq hdiff
  refine ⟨r - E₁.inr (op Y) n, ?_⟩
  rw [map_sub, e.inr_comm (op Y) n, hn, sub_sub_cancel]

/-- A local section of `𝒪₂` which is in the image of `𝒪₁` after restriction along every arrow
of a covering sieve is in the image. -/
theorem exists_app_eq_of_locally (e : Hom E₁ E₂) {X : Cᵒᵖ} (s : ↥(E₂.O.obj.obj X))
    {S : Sieve X.unop} (hS : S ∈ K X.unop)
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → ∃ t : ↥(E₁.O.obj.obj (op Y)),
      e.hom.hom.app (op Y) t = (E₂.O.obj.map f.op).hom s) :
    ∃ t : ↥(E₁.O.obj.obj X), e.hom.hom.app X t = s := by
  classical
  obtain ⟨t, ht, -⟩ := isSheaf_forgetCommRing E₁.O S hS
    (fun _ f hf => (hs f hf).choose) (by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
      refine e.app_injective (op Z) ?_
      have key : ∀ {Y : C} (g : Z ⟶ Y) (f : Y ⟶ X.unop) (h : S f),
          e.hom.hom.app (op Z) ((E₁.O.obj.map g.op).hom (hs f h).choose)
            = (E₂.O.obj.map g.op).hom ((E₂.O.obj.map f.op).hom s) := fun g f h =>
        (e.app_map g.op _).trans (congrArg (E₂.O.obj.map g.op).hom (hs f h).choose_spec)
      have hmaps : (E₂.O.obj.map g₁.op).hom ((E₂.O.obj.map f₁.op).hom s)
          = (E₂.O.obj.map g₂.op).hom ((E₂.O.obj.map f₂.op).hom s) := by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg]
      exact (key g₁ f₁ h₁).trans (hmaps.trans (key g₂ f₂ h₂).symm))
  refine ⟨t, eq_of_locally_eq (isSheaf_forgetCommRing E₂.O) hS _ _ fun Y f hf => ?_⟩
  exact (e.app_map f.op t).symm.trans
    ((congrArg (e.hom.hom.app (op Y)) (ht f hf)).trans (hs f hf).choose_spec)

/-- **The five lemma, surjectivity.**  A morphism of extensions is surjective on sections. -/
theorem app_surjective (e : Hom E₁ E₂) (X : Cᵒᵖ) :
    Function.Surjective (e.hom.hom.app X) := fun s =>
  e.exists_app_eq_of_locally s
    (Presheaf.imageSieve_mem K E₁.proj.hom (E₂.proj.hom.app X s))
    fun _ f hf => e.exists_app_eq_locally s f hf

/-- **The five lemma.**  A morphism of extensions of `ℬ` by `𝒢` over `𝒜` is bijective on
sections. -/
theorem app_bijective (e : Hom E₁ E₂) (X : Cᵒᵖ) :
    Function.Bijective (e.hom.hom.app X) :=
  ⟨e.app_injective X, e.app_surjective X⟩

/-- The sectionwise ring isomorphism underlying a morphism of extensions. -/
def appRingEquiv (e : Hom E₁ E₂) (X : Cᵒᵖ) : ↥(E₁.O.obj.obj X) ≃+* ↥(E₂.O.obj.obj X) :=
  RingEquiv.ofBijective (e.hom.hom.app X).hom (e.app_bijective X)

/-- The ring isomorphism `e.appRingEquiv X` is the component of `e` at `X`. -/
@[simp] theorem appRingEquiv_apply (e : Hom E₁ E₂) (X : Cᵒᵖ) (s : ↥(E₁.O.obj.obj X)) :
    e.appRingEquiv X s = e.hom.hom.app X s := rfl

/-- The component of `e` at `X` sends `(e.appRingEquiv X).symm s` to `s`. -/
@[simp] theorem app_appRingEquiv_symm (e : Hom E₁ E₂) (X : Cᵒᵖ) (s : ↥(E₂.O.obj.obj X)) :
    e.hom.hom.app X ((e.appRingEquiv X).symm s) = s :=
  (e.appRingEquiv X).apply_symm_apply s

/-- The morphism of sheaves of rings inverse to a morphism of extensions. -/
def invHom (e : Hom E₁ E₂) : E₂.O ⟶ E₁.O :=
  ⟨{ app := fun X => CommRingCat.ofHom (e.appRingEquiv X).symm.toRingHom
     naturality := fun X Y f => by
       apply CommRingCat.hom_ext
       refine RingHom.ext fun s => e.app_injective Y ?_
       change e.hom.hom.app Y ((e.appRingEquiv Y).symm ((E₂.O.obj.map f).hom s))
           = e.hom.hom.app Y ((E₁.O.obj.map f).hom ((e.appRingEquiv X).symm s))
       exact (app_appRingEquiv_symm e Y ((E₂.O.obj.map f).hom s)).trans
         ((congrArg (E₂.O.obj.map f).hom (app_appRingEquiv_symm e X s)).symm.trans
           (e.app_map f ((e.appRingEquiv X).symm s)).symm) }⟩

/-- The component of `e.invHom` at `X` is the inverse of `e.appRingEquiv X`. -/
@[simp] theorem invHom_app (e : Hom E₁ E₂) (X : Cᵒᵖ) (s : ↥(E₂.O.obj.obj X)) :
    (e.invHom).hom.app X s = (e.appRingEquiv X).symm s := rfl

/-- The inverse morphism composed with the morphism is the identity. -/
theorem invHom_comp (e : Hom E₁ E₂) : e.invHom ≫ e.hom = 𝟙 E₂.O := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun s => ?_))
  exact app_appRingEquiv_symm e X s

/-- The morphism composed with the inverse morphism is the identity. -/
theorem comp_invHom (e : Hom E₁ E₂) : e.hom ≫ e.invHom = 𝟙 E₁.O := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun s => ?_))
  exact (e.appRingEquiv X).symm_apply_apply s

/-- **A morphism of extensions is an isomorphism of sheaves of commutative rings.** -/
theorem isIso (e : Hom E₁ E₂) : IsIso e.hom := ⟨e.invHom, e.comp_invHom, e.invHom_comp⟩

/-- The inverse of a morphism of extensions is a morphism of extensions. -/
def symm (e : Hom E₁ E₂) : Hom E₂ E₁ where
  hom := e.invHom
  base_comm := by rw [← e.base_comm, Category.assoc, e.comp_invHom, Category.comp_id]
  proj_comm := by rw [← e.proj_comm, ← Category.assoc, e.invHom_comp, Category.id_comp]
  inr_comm X n := e.app_injective X (by
    rw [invHom_app, app_appRingEquiv_symm, e.inr_comm X n])

/-- The identity morphism of an extension. -/
def id (E : AlgebraExtension A B base G) : Hom E E where
  hom := 𝟙 E.O
  base_comm := Category.comp_id _
  proj_comm := Category.id_comp _
  inr_comm _ _ := rfl

/-- The composite of two morphisms of extensions. -/
@[ega "0 18.2.4" "special case"]
def comp (e : Hom E₁ E₂) (f : Hom E₂ E₃) : Hom E₁ E₃ where
  hom := e.hom ≫ f.hom
  base_comm := by rw [← Category.assoc, e.base_comm, f.base_comm]
  proj_comm := by rw [Category.assoc, f.proj_comm, e.proj_comm]
  inr_comm X n := by
    change f.hom.hom.app X (e.hom.hom.app X (E₁.inr X n)) = _
    rw [e.inr_comm X n, f.inr_comm X n]

end Hom

/-- Two extensions of `ℬ` by `𝒢` over `𝒜` are **isomorphic** when there is a morphism of
extensions between them.  By `AlgebraExtension.Hom.isIso` such a morphism is automatically an
isomorphism of sheaves of commutative rings, and by `AlgebraExtension.Hom.symm` the relation is
symmetric. -/
def Isomorphic (E₁ E₂ : AlgebraExtension A B base G) : Prop := Nonempty (Hom E₁ E₂)

namespace Isomorphic

variable {E₁ E₂ E₃ : AlgebraExtension A B base G}

/-- Isomorphy of extensions is reflexive. -/
theorem refl (E : AlgebraExtension A B base G) : Isomorphic E E := ⟨Hom.id E⟩

/-- Isomorphy of extensions is symmetric. -/
theorem symm (h : Isomorphic E₁ E₂) : Isomorphic E₂ E₁ := ⟨(Nonempty.some h).symm⟩

/-- Isomorphy of extensions is transitive. -/
theorem trans (h : Isomorphic E₁ E₂) (h' : Isomorphic E₂ E₃) : Isomorphic E₁ E₃ :=
  ⟨(Nonempty.some h).comp (Nonempty.some h')⟩

/-- Two isomorphic extensions have isomorphic middle sheaves of rings: the chosen morphism of
extensions between them is an isomorphism. -/
theorem isIso (h : Isomorphic E₁ E₂) : IsIso (Nonempty.some h).hom :=
  (Nonempty.some h).isIso

end Isomorphic

end AlgebraExtension

end Stacks.Sites.SqZeroExtension

end
