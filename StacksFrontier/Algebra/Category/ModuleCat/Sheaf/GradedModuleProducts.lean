module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# Products of graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras. The
category of right graded `A`-modules has arbitrary products, formed degreewise: the degree-`n`
piece of the product is the product of the degree-`n` pieces, and the action of `A` is the
coordinatewise one.

## Main results

* `SheafOfModules.GradedModule.hasProducts`: right graded modules over a sheaf of graded
  algebras admit arbitrary products.

## Implementation notes

Unlike direct sums, a product of sheaves of modules needs no sheafification: it is the
sectionwise product, which Mathlib provides as `CategoryTheory.Limits.limit` of a discrete
diagram in `SheafOfModules.{m} R`. So the product of graded modules is built directly, with no
presheaf-level intermediate.

Even so the product has no *definitional* description on sections, so the action is specified
through the isomorphism `productSectionIso` between the sections of the degreewise product and
the product of the sections. That isomorphism is the composite of the preservation isomorphism
of `SheafOfModules.evaluation` with the comparison of the resulting limit in `ModuleCat` against
the concrete `modulePiLimitCone`; `productSectionIso_π` identifies its coordinates with the
limit projections, and every structure field of the product is then checked one coordinate at a
time, the coordinates being separated by `productSectionIso_injective`.

The associativity and unit laws of the action relate sections in propositionally — but not
definitionally — equal degrees. They are therefore stated with `HEq` and proved by transporting
along the degree equality: `productSectionIso_cast` commutes the section isomorphism past such a
transport, and `productCoordinates_cast_apply` evaluates a transported dependent function at an
index.

Restriction maps are written through `Stacks.restr` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`, whose whole purpose is
this: a term that puts `N.map f x` where `N.obj V` is expected elaborates, but is not
type-correct at the transparency `rw` uses to build its motive, so a rewrite in the naturality
of the action fails without it.

The index type lies in the universe of the module sections. This is forced, not a narrowing:
`SheafOfModules.{m} R` has limits only of diagrams small relative to `m`, and
`CategoryTheory.Limits.HasProducts.{m}` is exactly the statement for index types in `Type m`.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m w v u

namespace SheafOfModules

namespace GradedModule

/-- The concrete product cone of a discrete diagram of modules, with the dependent function
type as its vertex. -/
private def modulePiLimitCone {S : Type t} [Ring S] {ι : Type m}
    (K : Discrete ι ⥤ ModuleCat S) : LimitCone K where
  cone :=
    { pt := ModuleCat.of S (∀ i, K.obj ⟨i⟩)
      π :=
        { app := fun i => ModuleCat.ofHom (LinearMap.proj i.as)
          naturality := by
            intro i j f
            cases i with
            | mk i =>
              cases j with
              | mk j =>
                have h : i = j := f.eq
                subst j
                have hf : f = 𝟙 (Discrete.mk i) := Subsingleton.elim _ _
                rw [hf]
                simp } }
  isLimit :=
    { lift := fun s => ModuleCat.ofHom
        (LinearMap.pi fun i => (s.π.app ⟨i⟩).hom)
      fac := by
        intro s i
        apply ModuleCat.hom_ext
        ext x
        rfl
      uniq := by
        intro s m hm
        apply ModuleCat.hom_ext
        ext x i
        simpa using congrArg (fun f => f.hom x) (hm ⟨i⟩) }

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The degree-`n` piece of the product of a family of graded modules. -/
@[reducible] private noncomputable def productPieces
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) : SheafOfModules.{m} R :=
  limit (Discrete.functor fun i => (M i).piece n)

/-- The sections of the degreewise product are the product of the sections. -/
private noncomputable def productSectionIso
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) (U : Cᵒᵖ) :
    ModuleCat.of (R.obj.obj U) ((productPieces M n).val.obj U) ≅
      ModuleCat.of (R.obj.obj U) (∀ i, ((M i).piece n).val.obj U) := by
  let F : Discrete ι ⥤ SheafOfModules.{m} R := Discrete.functor fun i => (M i).piece n
  let G := SheafOfModules.evaluation R U
  let e := preservesLimitIso G F
  let t : LimitCone (F ⋙ G) := modulePiLimitCone (F ⋙ G)
  exact e.trans (limit.isoLimitCone t)

/-- The coordinates of `productSectionIso` are the limit projections. -/
private theorem productSectionIso_π
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) (U : Cᵒᵖ)
    (i : ι) (x : ((productPieces M n).val.obj U)) :
    (productSectionIso M n U).hom x i =
      ((limit.π (Discrete.functor fun j => (M j).piece n) ⟨i⟩).val.app U) x := by
  let F : Discrete ι ⥤ SheafOfModules.{m} R := Discrete.functor fun j => (M j).piece n
  let G := SheafOfModules.evaluation R U
  let e := preservesLimitIso G F
  let t : LimitCone (F ⋙ G) := modulePiLimitCone (F ⋙ G)
  let e₂ := limit.isoLimitCone t
  show (e₂.hom (e.hom x)) i = _
  have h₁ : (e₂.hom (e.hom x)) i = (limit.π (F ⋙ G) ⟨i⟩).hom (e.hom x) :=
    congrArg (fun f => f.hom (e.hom x)) (limit.isoLimitCone_hom_π t ⟨i⟩)
  have h₂ : (limit.π (F ⋙ G) ⟨i⟩).hom (e.hom x) = (G.map (limit.π F ⟨i⟩)).hom x :=
    congrArg (fun f => f.hom x) (preservesLimitIso_hom_π G F ⟨i⟩)
  rw [h₁, h₂]
  rfl

/-- Sections of the degreewise product are determined by their coordinates. -/
private theorem productSectionIso_injective
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) (U : Cᵒᵖ) :
    Function.Injective ((productSectionIso M n U).hom : _ → _) := by
  intro x y h
  have h' := congrArg (fun z => (productSectionIso M n U).inv z) h
  simpa using h'

/-- The coordinatewise action of the algebra on the degreewise product. -/
private noncomputable def productAction
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ) :
    (productPieces M n).val.obj U →+
      (A.piece i).val.obj U →+ (productPieces M (n + i)).val.obj U := by
  let eₙ := productSectionIso M n U
  let eₙᵢ := productSectionIso M (n + i) U
  have hinj : Function.Injective (eₙᵢ.hom : _ → _) := productSectionIso_injective M (n + i) U
  exact
    { toFun := fun x =>
        { toFun := fun b => eₙᵢ.inv (fun k => (M k).smul n i U (eₙ.hom x k) b)
          map_zero' := by
            apply hinj
            funext k
            simp only [ModuleCat.of_coe, map_zero, Iso.inv_hom_id_apply]
            change (0 : ((M k).piece (n + i)).val.obj U) = 0
            rfl
          map_add' := by
            intro b c
            apply hinj
            funext k
            simp [eₙᵢ, eₙ] }
      map_zero' := by
        ext b
        apply hinj
        funext k
        simp only [ModuleCat.of_coe, map_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Iso.inv_hom_id_apply, AddMonoidHom.zero_apply]
        change ((M k).smul n i U 0) b = 0
        rw [map_zero]
        simp
      map_add' := by
        intro x y
        ext b
        apply hinj
        funext k
        simp [eₙᵢ, eₙ] }

/-- The coordinates of the product action are the actions on the coordinates. -/
private theorem productAction_coordinate
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (productPieces M n).val.obj U) (b : (A.piece i).val.obj U) (k : ι) :
    (productSectionIso M (n + i) U).hom (productAction M n i U x b) k =
      (M k).smul n i U ((productSectionIso M n U).hom x k) b := by
  simp [productAction]

/-- The section isomorphism of the degreewise product is natural in the object of the site.

The restriction maps are written with `Stacks.restr` rather than as `.val.map f`, since a term
that puts `N.map f x` where `N.obj V` is expected is not type-correct at the transparency `rw`
uses to build its motive; see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`. -/
private theorem productSectionIso_restr
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (productPieces M n).val.obj U) (i : ι) :
    (productSectionIso M n V).hom (Stacks.restr (productPieces M n).val f x) i =
      Stacks.restr ((M i).piece n).val f ((productSectionIso M n U).hom x i) := by
  rw [productSectionIso_π, productSectionIso_π]
  exact Stacks.restr_app (limit.π (Discrete.functor fun j => (M j).piece n) ⟨i⟩).val f x

/-- Transporting a dependent function along an equality of degrees acts coordinatewise. -/
private theorem productCoordinates_cast_apply
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) {k l : ℤ} (h : k = l)
    (U : Cᵒᵖ) (x : ∀ i, ((M i).piece k).val.obj U) (i : ι) :
    (cast (congrArg (fun d => ∀ i, (show Type m from ((M i).piece d).val.obj U)) h) x :
      ∀ i, ((M i).piece l).val.obj U) i =
        cast (congrArg (fun d => (show Type m from ((M i).piece d).val.obj U)) h) (x i) := by
  cases h
  rfl

/-- The section isomorphism of the degreewise product commutes with a transport of degrees. -/
private theorem productSectionIso_cast
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) {k l : ℤ} (h : k = l)
    (U : Cᵒᵖ) (x : (productPieces M k).val.obj U) :
    (productSectionIso M l U).hom
        (cast (congrArg (fun d => (show Type m from (productPieces M d).val.obj U)) h) x) =
      cast (congrArg (fun d => ∀ i, (show Type m from ((M i).piece d).val.obj U)) h)
        ((productSectionIso M k U).hom x) := by
  cases h
  rfl

/-- The product of a family of graded modules, formed degreewise. -/
@[reducible] private noncomputable def productObject
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) : GradedModule.{t, a, m} A where
  piece := productPieces M
  smul := productAction M
  smul_smul_left := by
    intro n i U r x b
    apply productSectionIso_injective M (n + i) U
    funext k
    rw [productAction_coordinate, (productSectionIso M (n + i) U).hom.hom.map_smul, Pi.smul_apply,
      productAction_coordinate, (productSectionIso M n U).hom.hom.map_smul, Pi.smul_apply]
    exact (M k).smul_smul_left n i U r ((productSectionIso M n U).hom x k) b
  smul_smul_right := by
    intro n i U r x b
    apply productSectionIso_injective M (n + i) U
    funext k
    rw [(productSectionIso M (n + i) U).hom.hom.map_smul, Pi.smul_apply,
      productAction_coordinate, productAction_coordinate]
    exact (M k).smul_smul_right n i U r _ b
  smul_naturality := by
    intro n i U V f x b
    change Stacks.restr (productPieces M (n + i)).val f (productAction M n i U x b)
      = productAction M n i V (Stacks.restr (productPieces M n).val f x)
          (Stacks.restr (A.piece i).val f b)
    apply productSectionIso_injective M (n + i) V
    funext k
    rw [productSectionIso_restr M (n + i) f, productAction_coordinate,
      productAction_coordinate, productSectionIso_restr M n f]
    exact (M k).smul_naturality n i f _ _
  smul_mul := by
    intro n i j U x b c
    let hdeg : (n + i) + j = n + (i + j) := Int.add_assoc n i j
    apply heq_of_cast_eq
      (congrArg (fun d => (show Type m from (productPieces M d).val.obj U)) hdeg)
    apply productSectionIso_injective M (n + (i + j)) U
    rw [productSectionIso_cast M hdeg]
    funext k
    change (cast (congrArg (fun d => ∀ k, (show Type m from ((M k).piece d).val.obj U)) hdeg)
      ((productSectionIso M ((n + i) + j) U).hom
        (productAction M (n + i) j U (productAction M n i U x b) c)) :
        ∀ k, ((M k).piece (n + (i + j))).val.obj U) k = _
    rw [productCoordinates_cast_apply, productAction_coordinate,
      productAction_coordinate, productAction_coordinate]
    all_goals first
      | exact hdeg
      | exact cast_eq_iff_heq.mpr ((M k).smul_mul n i j U _ b c)
  smul_one := by
    intro n U x
    let hdeg : n + 0 = n := Int.add_zero n
    apply heq_of_cast_eq
      (congrArg (fun d => (show Type m from (productPieces M d).val.obj U)) hdeg)
    apply productSectionIso_injective M n U
    rw [productSectionIso_cast M hdeg]
    funext i
    change (cast (congrArg (fun d => ∀ i, (show Type m from ((M i).piece d).val.obj U)) hdeg)
      ((productSectionIso M (n + 0) U).hom
        (productAction M n 0 U x (A.one.eval U))) :
        ∀ i, ((M i).piece n).val.obj U) i = _
    rw [productCoordinates_cast_apply, productAction_coordinate]
    all_goals first
      | exact hdeg
      | exact cast_eq_iff_heq.mpr ((M i).smul_one n U _)

/-- The homomorphism into the degreewise product determined by a fan of graded modules. -/
private noncomputable def productLift
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (s : Fan M) : Hom s.pt (productObject M) where
  app n := limit.lift (Discrete.functor fun i => (M i).piece n)
    (Fan.mk (s.pt.piece n) fun i => (s.π.app ⟨i⟩).app n)
  map_smul := by
    intro n i U x b
    dsimp [productObject, productPieces]
    apply productSectionIso_injective M (n + i) U
    funext k
    change (productSectionIso M (n + i) U).hom
        ((limit.lift (Discrete.functor fun j => (M j).piece (n + i))
          (Fan.mk (s.pt.piece (n + i)) fun j => (s.π.app ⟨j⟩).app (n + i))).val.app U
          ((s.pt.smul n i U) x b)) k =
      (productSectionIso M (n + i) U).hom
        (productAction M n i U
          ((limit.lift (Discrete.functor fun j => (M j).piece n)
            (Fan.mk (s.pt.piece n) fun j => (s.π.app ⟨j⟩).app n)).val.app U x) b) k
    rw [productSectionIso_π, productAction_coordinate, productSectionIso_π M n U k]
    let cₙᵢ := Fan.mk (s.pt.piece (n + i)) fun j => (s.π.app ⟨j⟩).app (n + i)
    let cₙ := Fan.mk (s.pt.piece n) fun j => (s.π.app ⟨j⟩).app n
    have hₙᵢ :
        ((limit.π (Discrete.functor fun j => (M j).piece (n + i)) ⟨k⟩).val.app U)
            ((limit.lift (Discrete.functor fun j => (M j).piece (n + i)) cₙᵢ).val.app U
              ((s.pt.smul n i U) x b)) =
          ((s.π.app ⟨k⟩).app (n + i)).val.app U ((s.pt.smul n i U) x b) :=
      congrArg (fun g => g.val.app U ((s.pt.smul n i U) x b)) (limit.lift_π cₙᵢ ⟨k⟩)
    have hₙ :
        ((limit.π (Discrete.functor fun j => (M j).piece n) ⟨k⟩).val.app U)
            ((limit.lift (Discrete.functor fun j => (M j).piece n) cₙ).val.app U x) =
          ((s.π.app ⟨k⟩).app n).val.app U x :=
      congrArg (fun g => g.val.app U x) (limit.lift_π cₙ ⟨k⟩)
    rw [hₙᵢ, hₙ]
    exact (s.π.app ⟨k⟩).map_smul n i U x b

/-- The degreewise product, as a fan of graded modules. -/
@[reducible] private noncomputable def productFan
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) : Fan M :=
  Fan.mk (productObject M) fun i =>
    { app n := limit.π (Discrete.functor fun j => (M j).piece n) ⟨i⟩
      map_smul := by
        intro n j U x b
        dsimp [productObject, productPieces] at x ⊢
        change ((limit.π (Discrete.functor fun l => (M l).piece (n + j)) ⟨i⟩).val.app U)
            (productAction M n j U x b) =
          (M i).smul n j U
            (((limit.π (Discrete.functor fun l => (M l).piece n) ⟨i⟩).val.app U) x) b
        rw [← productSectionIso_π M (n + j) U i,
          ← productSectionIso_π M n U i, productAction_coordinate] }

/-- The degreewise product of graded modules is their product. -/
private noncomputable def productFanIsLimit
    {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) : IsLimit (productFan M) where
  lift := productLift M
  fac := by
    intro s i
    apply Hom.ext
    intro n
    change (limit.lift (Discrete.functor fun j => (M j).piece n)
        (Fan.mk (s.pt.piece n) fun j => (s.π.app ⟨j⟩).app n) ≫
      limit.π (Discrete.functor fun j => (M j).piece n) i) = (s.π.app i).app n
    exact limit.lift_π _ _
  uniq := by
    intro s f hf
    apply Hom.ext
    intro n
    change f.app n = limit.lift (Discrete.functor fun j => (M j).piece n)
      (Fan.mk (s.pt.piece n) fun j => (s.π.app ⟨j⟩).app n)
    apply (limit.isLimit (Discrete.functor fun j => (M j).piece n)).hom_ext
    intro i
    have hi : (f ≫ (productFan M).π.app i).app n = (s.π.app i).app n := by rw [hf i]
    have hLift : (limit.lift (Discrete.functor fun j => (M j).piece n)
        (Fan.mk (s.pt.piece n) fun j => (s.π.app ⟨j⟩).app n)) ≫
          limit.π (Discrete.functor fun j => (M j).piece n) i = (s.π.app i).app n := by simp
    change f.app n ≫ limit.π (Discrete.functor fun j => (M j).piece n) i =
      (s.π.app i).app n at hi
    exact hi.trans hLift.symm

/-- Right graded modules over a sheaf of graded algebras admit arbitrary products, formed
degreewise. -/
instance hasProducts (A : GradedAlgebra.{t, a} R) :
    HasProducts.{m} (GradedModule.{t, a, m} A) :=
  hasProducts_of_limit_fans
    (fun {ι : Type m} (M : ι → GradedModule.{t, a, m} A) => productFan M)
    (fun {ι : Type m} (M : ι → GradedModule.{t, a, m} A) => productFanIsLimit M)

/-- Taking a fixed homogeneous component preserves products: the degreewise product fan of a
family of graded modules is sent to a product fan of their degree-`n` pieces, which it is by
construction. -/
instance pieceFunctor_preservesProduct {A : GradedAlgebra.{t, a} R} {ι : Type m}
    (M : ι → GradedModule.{t, a, m} A) (n : ℤ) :
    PreservesLimit (Discrete.functor M) (pieceFunctor.{t, a, m} A n) :=
  preservesLimit_of_preserves_limit_cone (productFanIsLimit M)
    ((isLimitMapConeFanMkEquiv (pieceFunctor.{t, a, m} A n) M
      (fun i => (productFan M).π.app ⟨i⟩)).symm
      (limit.isLimit (Discrete.functor fun i => (M i).piece n)))

end GradedModule

end SheafOfModules
