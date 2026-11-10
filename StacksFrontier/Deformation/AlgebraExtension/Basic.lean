module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestrictionSupplement

/-!
# Square-zero extensions of sheaves of algebras

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a site and let `ℳ` be a sheaf
of `𝒪`-modules. An *extension of `𝒜`-algebras of `𝒪` by `ℳ`* is a sheaf of commutative rings
`𝒪'` with a locally surjective map `𝒪' ⟶ 𝒪` of `𝒜`-algebras whose kernel is a square-zero ideal
identified with `ℳ`:

`0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0`.

A morphism along a map `φ : ℳ ⟶ 𝒩` of modules is a map of the middle terms over `𝒪`, under
`𝒜`, inducing `φ` on the ideals; for `φ` the identity these are the morphisms of the category of
extensions by `ℳ`.

## Main definitions

* `Deformation.AlgebraExtension`: an extension of `𝒜`-algebras of `𝒪` by `ℳ`.
* `Deformation.AlgebraExtension.MapAlong`: a morphism of extensions inducing a given map of
  ideal modules.
* `Deformation.AlgebraExtension.instCategory`: the category of extensions by `ℳ`.
* `Deformation.AlgebraExtension.IsPushoutFunctor`: the universal property of pushout along `φ`.

## Main results

* `Deformation.AlgebraExtension.MapAlong.injective_app` and
  `Deformation.AlgebraExtension.MapAlong.isLocallySurjective`: the short five lemma on the two
  ideal rows, section by section.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Deformation

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}}

/-- **An extension of `𝒜`-algebras of `𝒪` by `ℳ`**: a sheaf of commutative rings `𝒪'` with a
locally surjective homomorphism `𝒪' ⟶ 𝒪` of `𝒜`-algebras whose kernel has square zero and is
identified, section by section, with the `𝒪`-module `ℳ`. -/
structure AlgebraExtension (a : A ⟶ O)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) where
  /-- The middle term `𝒪'`. -/
  extension : Sheaf J CommRingCat.{u}
  /-- The reduction `𝒪' ⟶ 𝒪`. -/
  reduction : extension ⟶ O
  /-- The reduction is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective J reduction.hom
  /-- The kernel of the reduction has square zero. -/
  squareZero : ∀ U : Cᵒᵖ, (RingHom.ker (reduction.hom.app U).hom) ^ 2 = ⊥
  /-- The `𝒜`-algebra structure of `𝒪'`. -/
  algebraMap : A ⟶ extension
  /-- The reduction is a homomorphism of `𝒜`-algebras. -/
  algebraMap_reduction : algebraMap ≫ reduction = a
  /-- The identification of `ℳ` with the kernel of the reduction. -/
  kernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map reduction)).obj M ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj extension)
  /-- The image of `ℳ` is killed by the reduction. -/
  kernelZero : ∀ (U : Cᵒᵖ) (m : M.val.obj U),
    reduction.hom.app U ((kernelInclusion.val.app U m) : extension.obj.obj U) = 0
  /-- `ℳ` is the whole kernel of the reduction, uniquely, on every section. -/
  kernelUniversal : ∀ (U : Cᵒᵖ) (x : extension.obj.obj U), reduction.hom.app U x = 0 →
    ∃! m : M.val.obj U, ((kernelInclusion.val.app U m) : extension.obj.obj U) = x

namespace AlgebraExtension

variable {a : A ⟶ O}
  {M N L : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- A section of `𝒪`, read as a scalar of the sheaf of modules `ℳ`. -/
abbrev scalar {U : Cᵒᵖ} (x : O.obj.obj U) :
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj U := x

/-- The section of `𝒪'` attached to a section of `ℳ`. -/
noncomputable def incl (P : AlgebraExtension a M) {U : Cᵒᵖ} (m : M.val.obj U) :
    P.extension.obj.obj U :=
  P.kernelInclusion.val.app U m

/-- The section of `𝒪'` attached to a sum is the sum of the sections. -/
theorem incl_add (P : AlgebraExtension a M) {U : Cᵒᵖ} (m n : M.val.obj U) :
    P.incl (m + n) = P.incl m + P.incl n :=
  map_add (P.kernelInclusion.val.app U).hom m n

/-- The section of `𝒪'` attached to zero is zero. -/
theorem incl_zero (P : AlgebraExtension a M) {U : Cᵒᵖ} : P.incl (0 : M.val.obj U) = 0 :=
  map_zero (P.kernelInclusion.val.app U).hom

/-- The section of `𝒪'` attached to a difference is the difference of the sections. -/
theorem incl_sub (P : AlgebraExtension a M) {U : Cᵒᵖ} (m n : M.val.obj U) :
    P.incl (m - n) = P.incl m - P.incl n :=
  map_sub (P.kernelInclusion.val.app U).hom m n

/-- The section of `𝒪'` attached to a negative is the negative of the section. -/
theorem incl_neg (P : AlgebraExtension a M) {U : Cᵒᵖ} (m : M.val.obj U) :
    P.incl (-m) = -P.incl m :=
  map_neg (P.kernelInclusion.val.app U).hom m

/-- The reduction kills the section of `𝒪'` attached to a section of `ℳ`. -/
theorem reduction_incl (P : AlgebraExtension a M) {U : Cᵒᵖ} (m : M.val.obj U) :
    P.reduction.hom.app U (P.incl m) = 0 :=
  P.kernelZero U m

/-- Distinct sections of `ℳ` give distinct sections of `𝒪'`. -/
theorem incl_injective (P : AlgebraExtension a M) {U : Cᵒᵖ} :
    Function.Injective (P.incl (U := U)) := by
  intro m n h
  obtain ⟨p, -, hp⟩ := P.kernelUniversal U (P.incl m) (P.kernelZero U m)
  exact (hp m rfl).trans (hp n h.symm).symm

/-- A section of `𝒪'` killed by the reduction comes from a section of `ℳ`. -/
theorem exists_incl (P : AlgebraExtension a M) {U : Cᵒᵖ} (x : P.extension.obj.obj U)
    (hx : P.reduction.hom.app U x = 0) : ∃ m : M.val.obj U, P.incl m = x := by
  obtain ⟨m, hm, -⟩ := P.kernelUniversal U x hx
  exact ⟨m, hm⟩

/-- The sections of `𝒪'` attached to sections of `ℳ` are compatible with restriction. -/
theorem incl_naturality (P : AlgebraExtension a M) {U V : Cᵒᵖ} (h : U ⟶ V)
    (m : M.val.obj U) :
    P.incl (U := V) (M.val.map h m) = P.extension.obj.map h (P.incl m) :=
  PresheafOfModules.naturality_apply P.kernelInclusion.val h m

/-- Scalars act on the ideal through the reduction. -/
theorem mul_incl (P : AlgebraExtension a M) {U : Cᵒᵖ} (x : P.extension.obj.obj U)
    (m : M.val.obj U) :
    x * P.incl m = P.incl (scalar (P.reduction.hom.app U x) • m) :=
  ((P.kernelInclusion.val.app U).hom.map_smul' x m).symm

/-- The ideal has square zero. -/
theorem incl_mul_incl (P : AlgebraExtension a M) {U : Cᵒᵖ} (m n : M.val.obj U) :
    P.incl m * P.incl n = 0 := by
  rw [P.mul_incl, P.reduction_incl]
  exact (congrArg P.incl (zero_smul _ n)).trans P.incl_zero

/-- The reduction of a section in the image of `𝒜`. -/
theorem reduction_algebraMap (P : AlgebraExtension a M) {U : Cᵒᵖ} (r : A.obj.obj U) :
    P.reduction.hom.app U (P.algebraMap.hom.app U r) = a.hom.app U r :=
  congrArg (fun k : A ⟶ O => k.hom.app U r) P.algebraMap_reduction

/-- **A morphism of extensions along `φ : ℳ ⟶ 𝒩`**: a homomorphism of the middle terms over
`𝒪` and under `𝒜` inducing `φ` on the identified ideals. For `φ = 𝟙` these are the morphisms
of the category of extensions by `ℳ`. -/
structure MapAlong (φ : M ⟶ N) (P : AlgebraExtension a M) (Q : AlgebraExtension a N) where
  /-- The homomorphism of middle terms. -/
  hom : P.extension ⟶ Q.extension
  /-- It is over `𝒪`. -/
  reduction_comm : hom ≫ Q.reduction = P.reduction
  /-- It is under `𝒜`. -/
  algebraMap_comm : P.algebraMap ≫ hom = Q.algebraMap
  /-- It induces `φ` on the ideals. -/
  kernel_comm : ∀ (U : Cᵒᵖ) (m : M.val.obj U),
    hom.hom.app U (P.incl m) = Q.incl ((φ.val.app U m) : N.val.obj U)

namespace MapAlong

variable {φ : M ⟶ N} {P : AlgebraExtension a M} {Q : AlgebraExtension a N}

/-- Two morphisms of extensions with the same homomorphism of middle terms are equal. -/
@[ext]
theorem ext {f g : MapAlong φ P Q} (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

/-- A morphism of extensions commutes with the reductions, section by section. -/
theorem reduction_apply (f : MapAlong φ P Q) {U : Cᵒᵖ} (x : P.extension.obj.obj U) :
    Q.reduction.hom.app U (f.hom.hom.app U x) = P.reduction.hom.app U x :=
  congrArg (fun k : P.extension ⟶ O => k.hom.app U x) f.reduction_comm

/-- A morphism of extensions commutes with the maps from `𝒜`, section by section. -/
theorem algebraMap_apply (f : MapAlong φ P Q) {U : Cᵒᵖ} (r : A.obj.obj U) :
    f.hom.hom.app U (P.algebraMap.hom.app U r) = Q.algebraMap.hom.app U r :=
  congrArg (fun k : A ⟶ Q.extension => k.hom.app U r) f.algebraMap_comm

/-- The composite of two morphisms of extensions, along any map of modules equal to the
composite of the two. -/
def comp {ψ : N ⟶ L} {χ : M ⟶ L} {R : AlgebraExtension a L} (f : MapAlong φ P Q)
    (g : MapAlong ψ Q R) (h : φ ≫ ψ = χ) : MapAlong χ P R where
  hom := f.hom ≫ g.hom
  reduction_comm := by rw [Category.assoc, g.reduction_comm, f.reduction_comm]
  algebraMap_comm := by rw [← Category.assoc, f.algebraMap_comm, g.algebraMap_comm]
  kernel_comm U m := by
    change g.hom.hom.app U (f.hom.hom.app U (P.incl m)) = _
    rw [f.kernel_comm, g.kernel_comm, ← h]
    rfl

/-- The homomorphism of middle terms of a composite is the composite of the homomorphisms. -/
@[simp]
theorem comp_hom {ψ : N ⟶ L} {χ : M ⟶ L} {R : AlgebraExtension a L} (f : MapAlong φ P Q)
    (g : MapAlong ψ Q R) (h : φ ≫ ψ = χ) : (f.comp g h).hom = f.hom ≫ g.hom :=
  rfl

/-- **A morphism of extensions along an injective map is injective on sections.** -/
theorem injective_app (f : MapAlong φ P Q)
    (hφ : ∀ U : Cᵒᵖ, Function.Injective (φ.val.app U)) (U : Cᵒᵖ) :
    Function.Injective (f.hom.hom.app U) := by
  intro x y hxy
  have hd : f.hom.hom.app U (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hr : P.reduction.hom.app U (x - y) = 0 := by rw [← f.reduction_apply, hd, map_zero]
  obtain ⟨m, hm⟩ := P.exists_incl (x - y) hr
  have h1 : Q.incl ((φ.val.app U m) : N.val.obj U) = 0 := by
    rw [← f.kernel_comm U m, hm, hd]
  have h2 : m = 0 := hφ U ((Q.incl_injective (h1.trans Q.incl_zero.symm)).trans
    (map_zero (φ.val.app U).hom).symm)
  rw [← sub_eq_zero, ← hm, h2, P.incl_zero]

/-- **A morphism of extensions along a surjective map is locally surjective.** -/
theorem isLocallySurjective (f : MapAlong φ P Q)
    (hφ : ∀ U : Cᵒᵖ, Function.Surjective (φ.val.app U)) :
    Presheaf.IsLocallySurjective J f.hom.hom where
  imageSieve_mem {U} y := by
    refine J.superset_covering ?_
      (P.locallySurjective.imageSieve_mem (Q.reduction.hom.app (op U) y))
    rintro V g ⟨x, hx⟩
    have hnat : Q.reduction.hom.app (op V) (Q.extension.obj.map g.op y) =
        O.obj.map g.op (Q.reduction.hom.app (op U) y) :=
      NatTrans.naturality_apply Q.reduction.hom g.op y
    have hdiff : Q.reduction.hom.app (op V)
        (f.hom.hom.app (op V) x - Q.extension.obj.map g.op y) = 0 := by
      rw [map_sub, f.reduction_apply x, hx, hnat, sub_self]
    obtain ⟨n, hn⟩ := Q.exists_incl _ hdiff
    obtain ⟨m, hm⟩ := hφ (op V) n
    refine ⟨x - P.incl m, ?_⟩
    rw [map_sub, f.kernel_comm (op V) m]
    change _ - Q.incl (φ.val.app (op V) m) = _
    rw [hm, hn, sub_sub_cancel]

end MapAlong

/-- **The category of extensions of `𝒜`-algebras of `𝒪` by `ℳ`**: the morphisms are the
morphisms of extensions inducing the identity on `ℳ`. -/
instance instCategory : Category (AlgebraExtension a M) where
  Hom P Q := MapAlong (𝟙 M) P Q
  id _ :=
    { hom := 𝟙 _
      reduction_comm := Category.id_comp _
      algebraMap_comm := Category.comp_id _
      kernel_comm := fun _ _ => rfl }
  comp f g := MapAlong.comp f g (Category.comp_id _)
  id_comp _ := MapAlong.ext (Category.id_comp _)
  comp_id _ := MapAlong.ext (Category.comp_id _)
  assoc _ _ _ := MapAlong.ext (Category.assoc _ _ _)

/-- The identity morphism of an extension is the identity of its middle term. -/
@[simp]
theorem id_hom (P : AlgebraExtension a M) : MapAlong.hom (𝟙 P) = 𝟙 P.extension :=
  rfl

/-- The homomorphism of middle terms of a composite in the category of extensions is the
composite of the homomorphisms. -/
@[simp]
theorem comp_hom' {P Q R : AlgebraExtension a M} (f : P ⟶ Q) (g : Q ⟶ R) :
    MapAlong.hom (f ≫ g) = MapAlong.hom f ≫ MapAlong.hom g :=
  rfl

/-- **The universal property of pushout along `φ`**: a morphism of extensions `ι_P : P ⟶ F(P)`
along `φ`, natural in `P`, through which every morphism of extensions along `φ` out of `P`
factors uniquely. -/
structure IsPushoutFunctor (φ : M ⟶ N) (F : AlgebraExtension a M ⥤ AlgebraExtension a N) where
  /-- The comparison morphism `P ⟶ F(P)` along `φ`. -/
  ι : ∀ P, MapAlong φ P (F.obj P)
  /-- It is natural. -/
  naturality : ∀ {P P' : AlgebraExtension a M} (k : P ⟶ P'),
    (ι P).hom ≫ (F.map k).hom = k.hom ≫ (ι P').hom
  /-- Every morphism along `φ` out of `P` factors uniquely through it. -/
  desc_unique : ∀ (P : AlgebraExtension a M) (Q : AlgebraExtension a N) (h : MapAlong φ P Q),
    ∃! k : F.obj P ⟶ Q, (ι P).hom ≫ k.hom = h.hom

end AlgebraExtension

end Deformation
