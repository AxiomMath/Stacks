module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantBundleIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleOver

/-!
# The determinant restricted to a slice site

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `F` a sheaf of modules over the
underlying sheaf of rings, `A` a bundle of tensor, exterior and symmetric algebras of `F`, and
`U : C`. Let `B` be any such bundle for `F|_U` on the slice site `(Over U, J.over U)`. This file
proves

`det(F)|_U ≅ det(F|_U)`,

the determinant of [Stacks, Tag 0FJN] — the annihilator of the degree-one part of the exterior
algebra, summed over the degrees — carried across the restriction to a slice site.

The input that makes this possible is
`SheafOfModules.isExteriorAlgebra_over`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra`): the restriction of an
exterior algebra of `F` is an exterior algebra of `F|_U` *with its algebra structure*, so the
comparison `SheafOfModules.exteriorOverIso` of the restricted exterior powers with those of `B`
comes with `exteriorOverIso_generator` and `exteriorOverIso_mul`. Those two compatibilities are
exactly what `SheafOfModules.TensorExteriorSymmetricAlgebras.IsExteriorAnnihilated` is phrased
in, and they are what the same-site argument of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantBundleIso` runs on.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorOverPieceIso`: the degreewise
  comparison of `A`'s exterior algebra restricted to the slice site with `B`'s.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorOverIso`: **the restricted
  degree-`n` annihilator is the degree-`n` annihilator of `B`**, as an isomorphism of the
  subsheaves.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantOverIso`: **`det(F)|_U ≅
  det(F|_U)`.**
* `CategoryTheory.Over.ofArrowOut` and `homOfArrowOut`: the object and the arrow of the slice
  site attached to an arrow out of `V.left` in `C`.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_over` and
  `isExteriorAnnihilated_of_over`: **the annihilator condition crosses the restriction in both
  directions.** This is the content of the file; everything else is assembly.

## Implementation notes

**Why the quantifier crosses with nothing to prove.** `IsExteriorAnnihilated A n x` for a
section `x` over `V.left` quantifies over all arrows `V.left ⟶ W` of `C` and all sections of `F`
there, while `IsExteriorAnnihilated B n y` quantifies over all arrows of `Over U` out of `V`.
The two ranges are the same datum: an arrow `g : W ⟶ V.left` of `C` makes `W` an object over `U`
by `g ≫ V.hom`, which is `CategoryTheory.Over.ofArrowOut`, and conversely an arrow of `Over U`
out of `V` is such a `g` by `Over.Hom.left`. So neither direction needs essential surjectivity
of the restriction functor; what the reverse direction *does* need, and uses, is that the
comparison of exterior powers is an isomorphism, so that an identity pushed forward along it can
be pulled back.

**Why the round trips are proved without `rw` or `simp`.** The objects
`(A.exteriorPower n).over U` and `B.exteriorPower n` live in
`SheafOfModules ((toRingCat J Osharp).over U)` and
`SheafOfModules (toRingCat (J.over U) (Osharp.over U))`, which are definitionally equal
categories with distinct spellings. A composite spanning the two elaborates but is not
type-correct at `implicit` transparency, so `rw [Category.assoc]` and `simp` both fail on the two
round-trip equations — `simp` reports that it made no progress. Each associativity step and each
congruence is therefore supplied as a fully applied term, which is defeq-tolerant. The same
crossing is why `exteriorOverPieceIso_mul` is stated at the `(A.exterior.mul i j).app
(op V.left)` spelling rather than at `((A.exterior.over U).mul i j).app V`: the two are equal by
`SheafOfModules.GradedAlgebra.over_mul_app`, which is `rfl`, but `rw` needs the spelling the
annihilator condition is written at.

**Why `HasBinaryProducts C` appears, and only at the last declaration.** Restriction to a slice
site is a left adjoint — its right adjoint is pushforward along `Over.star U`, which is where
binary products of the site are used — and that is how it is seen to preserve the `ℕ`-indexed
coproduct that `det` is. The degreewise statements need nothing of the kind. On the site of
opens of a topological space the hypothesis is automatic.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] (U : C)

/-- **An arrow out of `V.left` in `C` is an arrow out of `V` in the slice site over `U`.** Its
source is the object over `U` given by the composite to `U`. -/
def ofArrowOut {V : (Over U)ᵒᵖ} {W : Cᵒᵖ} (g : Opposite.op (Opposite.unop V).left ⟶ W) :
    (Over U)ᵒᵖ :=
  Opposite.op (Over.mk (g.unop ≫ (Opposite.unop V).hom))

/-- The arrow of the slice site over `U` attached to an arrow out of `V.left` in `C`. -/
def homOfArrowOut {V : (Over U)ᵒᵖ} {W : Cᵒᵖ} (g : Opposite.op (Opposite.unop V).left ⟶ W) :
    V ⟶ ofArrowOut U g :=
  Quiver.Hom.op
    (Over.homMk (U := Over.mk (g.unop ≫ (Opposite.unop V).hom)) (V := Opposite.unop V)
      g.unop rfl)

end CategoryTheory.Over

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F) (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (B : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over U) (J.over U) (F.over U))

/-- The degreewise comparison of the restriction of `A`'s exterior algebra with `B`'s. -/
def exteriorOverPieceIso (n : ℤ) :
    (A.exterior.over U).piece n ≅ B.exterior.piece n :=
  SheafOfModules.exteriorOverIso F A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
    B.exterior_isExteriorAlgebra n

/-- The comparison carries `A`'s degree-one generator, read over `V.left`, to `B`'s. -/
theorem exteriorOverPieceIso_generator (V : (Over U)ᵒᵖ) (m : (F.over U).val.obj V) :
    (exteriorOverPieceIso A U B 1).hom.val.app V
        (A.exteriorGenerator.val.app (op (unop V).left) m) =
      B.exteriorGenerator.val.app V m :=
  SheafOfModules.hom_congr_app_apply
    (SheafOfModules.exteriorOverIso_generator F A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
      B.exterior_isExteriorAlgebra) V m

/-- The comparison is multiplicative on homogeneous local sections, with the multiplication of
`A.over U` written as `A`'s multiplication over the underlying object of `C`. -/
theorem exteriorOverPieceIso_mul (i j : ℤ) (V : (Over U)ᵒᵖ)
    (y : (A.exterior.piece i).val.obj (op (unop V).left))
    (z : (A.exterior.piece j).val.obj (op (unop V).left)) :
    (exteriorOverPieceIso A U B (i + j)).hom.val.app V
        ((A.exterior.mul i j).app (op (unop V).left) y z) =
      (B.exterior.mul i j).app V ((exteriorOverPieceIso A U B i).hom.val.app V y)
        ((exteriorOverPieceIso A U B j).hom.val.app V z) :=
  SheafOfModules.exteriorOverIso_mul F A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator
    B.exterior_isExteriorAlgebra i j V y z

/-- Naturality of the comparison, with both restriction maps written out. -/
theorem exteriorOverPieceIso_map (n : ℕ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : (A.exteriorPower n).val.obj (op (unop V).left)) :
    (B.exteriorPower n).val.map f ((exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V x) =
      (exteriorOverPieceIso A U B (n : ℤ)).hom.val.app W
        ((A.exteriorPower n).val.map (Quiver.Hom.op (Over.Hom.left f.unop)) x) :=
  (PresheafOfModules.naturality_apply (exteriorOverPieceIso A U B (n : ℤ)).hom.val f x).symm

/-- The comparison undoes its inverse on sections. -/
theorem exteriorOverPieceIso_hom_inv (n : ℤ) (V : (Over U)ᵒᵖ)
    (z : (B.exterior.piece n).val.obj V) :
    (exteriorOverPieceIso A U B n).hom.val.app V
        ((exteriorOverPieceIso A U B n).inv.val.app V z) = z :=
  SheafOfModules.iso_inv_hom_app_apply (exteriorOverPieceIso A U B n).symm V z

/-- The inverse of the comparison undoes it on sections. -/
theorem exteriorOverPieceIso_inv_hom (n : ℤ) (V : (Over U)ᵒᵖ)
    (z : ((A.exterior.over U).piece n).val.obj V) :
    (exteriorOverPieceIso A U B n).inv.val.app V
        ((exteriorOverPieceIso A U B n).hom.val.app V z) = z :=
  SheafOfModules.iso_inv_hom_app_apply (exteriorOverPieceIso A U B n) V z

/-- The comparison carries the product of a generator with a restricted section to the product of
the generator with the restriction of the image section. -/
private theorem exteriorOverPieceIso_generator_mul_map (n : ℕ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (m : (F.over U).val.obj W) (x : (A.exteriorPower n).val.obj (op (unop V).left)) :
    (exteriorOverPieceIso A U B (1 + (n : ℤ))).hom.val.app W
        ((A.exterior.mul 1 n).app (op (unop W).left)
          (A.exteriorGenerator.val.app (op (unop W).left) m)
          ((A.exteriorPower n).val.map (Quiver.Hom.op (Over.Hom.left f.unop)) x)) =
      (B.exterior.mul 1 n).app W (B.exteriorGenerator.val.app W m)
        ((B.exteriorPower n).val.map f ((exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V x)) := by
  rw [exteriorOverPieceIso_map, ← exteriorOverPieceIso_generator A U B W m]
  exact exteriorOverPieceIso_mul A U B 1 (n : ℤ) W _ _

/-- **The comparison carries an exterior annihilated section to an exterior annihilated
section.** An arrow of the slice site out of `V` is an arrow of `C` out of `V.left`, along which
the hypothesis is read; the generator and the multiplication are translated by
`exteriorOverPieceIso_generator` and `exteriorOverPieceIso_mul`, and the translated product is
the comparison applied to a product that vanishes. -/
theorem isExteriorAnnihilated_over (n : ℕ) {V : (Over U)ᵒᵖ}
    (x : (A.exteriorPower n).val.obj (op (unop V).left))
    (hx : A.IsExteriorAnnihilated n x) :
    B.IsExteriorAnnihilated n ((exteriorOverPieceIso A U B (n : ℤ)).hom.val.app V x) := by
  intro W f m
  have hx' := hx (op (unop W).left) (Quiver.Hom.op (Over.Hom.left f.unop)) m
  rw [PresheafOfModules.restrictₛₗ_apply] at hx'
  rw [PresheafOfModules.restrictₛₗ_apply, ← exteriorOverPieceIso_generator_mul_map A U B n f m x,
    hx']
  exact map_zero _

/-- **The inverse comparison carries an exterior annihilated section to an exterior annihilated
section.** Here the arrow is given in `C` and `CategoryTheory.Over.ofArrowOut` makes it an arrow
of the slice site, at which the hypothesis is read; the conclusion is pulled back through the
comparison, which is where its invertibility is used. -/
theorem isExteriorAnnihilated_of_over (n : ℕ) {V : (Over U)ᵒᵖ}
    (y : (B.exteriorPower n).val.obj V)
    (hy : B.IsExteriorAnnihilated n y) :
    A.IsExteriorAnnihilated n ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V y) := by
  intro W g m
  have hy' := hy _ (CategoryTheory.Over.homOfArrowOut U g) m
  rw [PresheafOfModules.restrictₛₗ_apply] at hy'
  have key := exteriorOverPieceIso_generator_mul_map A U B n
    (CategoryTheory.Over.homOfArrowOut U g) m ((exteriorOverPieceIso A U B (n : ℤ)).inv.val.app V y)
  rw [exteriorOverPieceIso_hom_inv, hy'] at key
  exact (exteriorOverPieceIso_inv_hom A U B (1 + (n : ℤ)) _ _).symm.trans
    ((congrArg _ key).trans (map_zero _))

/-- The values of `annₙ(A)|_U ⟶ ⋀ⁿ(F|_U)` lie in `annₙ(B)`: the hypothesis of
`SheafOfModules.Submodule.factorThru` for the forward comparison. -/
theorem over_ι_mem_exteriorAnnihilator (n : ℕ) (V : (Over U)ᵒᵖ)
    (y : ((A.exteriorAnnihilator n).over U).toSheafOfModules.val.obj V) :
    ((((A.exteriorAnnihilator n).over U).ι ≫
        (exteriorOverPieceIso A U B (n : ℤ)).hom).val.app V y) ∈
      (B.exteriorAnnihilator n).obj V :=
  (mem_exteriorAnnihilator_obj B n _).mpr
    (isExteriorAnnihilated_over A U B n
      (x := ((A.exteriorAnnihilator n).over U).ι.val.app V y)
      ((mem_exteriorAnnihilator_obj A n _).mp
        (Submodule.ι_val_app_mem ((A.exteriorAnnihilator n).over U) V y)))

/-- The values of `annₙ(B) ⟶ (⋀ⁿ F)|_U` lie in `annₙ(A)|_U`: the hypothesis of
`SheafOfModules.Submodule.factorThru` for the inverse comparison. -/
theorem over_inv_ι_mem_exteriorAnnihilator (n : ℕ) (V : (Over U)ᵒᵖ)
    (y : (B.exteriorAnnihilator n).toSheafOfModules.val.obj V) :
    (((B.exteriorAnnihilator n).ι ≫
        (exteriorOverPieceIso A U B (n : ℤ)).inv).val.app V y) ∈
      ((A.exteriorAnnihilator n).over U).obj V :=
  (mem_exteriorAnnihilator_obj A n _).mpr
    (isExteriorAnnihilated_of_over A U B n
      (y := (B.exteriorAnnihilator n).ι.val.app V y)
      ((mem_exteriorAnnihilator_obj B n _).mp
        (Submodule.ι_val_app_mem (B.exteriorAnnihilator n) V y)))

/-- The comparison `annₙ(A)|_U ⟶ annₙ(B)`: the restricted inclusion followed by the
comparison of exterior powers, factored through the annihilator of `B`. -/
def exteriorAnnihilatorOverHom (n : ℕ) :
    ((A.exteriorAnnihilator n).over U).toSheafOfModules ⟶
      (B.exteriorAnnihilator n).toSheafOfModules :=
  (B.exteriorAnnihilator n).factorThru
    (((A.exteriorAnnihilator n).over U).ι ≫ (exteriorOverPieceIso A U B (n : ℤ)).hom)
    (over_ι_mem_exteriorAnnihilator A U B n)

/-- The forward comparison of annihilators, composed with the inclusion of `annₙ(B)`, is the
restricted inclusion followed by the comparison of exterior powers. -/
@[reassoc (attr := simp)]
theorem exteriorAnnihilatorOverHom_ι (n : ℕ) :
    exteriorAnnihilatorOverHom A U B n ≫ (B.exteriorAnnihilator n).ι =
      ((A.exteriorAnnihilator n).over U).ι ≫ (exteriorOverPieceIso A U B (n : ℤ)).hom :=
  Submodule.factorThru_ι _ _ _

/-- The comparison `annₙ(B) ⟶ annₙ(A)|_U`. -/
def exteriorAnnihilatorOverInv (n : ℕ) :
    (B.exteriorAnnihilator n).toSheafOfModules ⟶
      ((A.exteriorAnnihilator n).over U).toSheafOfModules :=
  ((A.exteriorAnnihilator n).over U).factorThru
    ((B.exteriorAnnihilator n).ι ≫ (exteriorOverPieceIso A U B (n : ℤ)).inv)
    (over_inv_ι_mem_exteriorAnnihilator A U B n)

/-- The inverse comparison of annihilators, composed with the restricted inclusion, is the
inclusion of `annₙ(B)` followed by the inverse comparison of exterior powers. -/
@[reassoc (attr := simp)]
theorem exteriorAnnihilatorOverInv_ι (n : ℕ) :
    exteriorAnnihilatorOverInv A U B n ≫ ((A.exteriorAnnihilator n).over U).ι =
      (B.exteriorAnnihilator n).ι ≫ (exteriorOverPieceIso A U B (n : ℤ)).inv :=
  Submodule.factorThru_ι _ _ _

/-- **The restriction to the slice site of the degree-`n` exterior annihilator of `A` is the
degree-`n` exterior annihilator of `B`.** Both directions are the factorization of the
comparison of exterior powers through the annihilator, and the two round trips are equalities of
morphisms into a subsheaf, hence can be cancelled against its inclusion. -/
def exteriorAnnihilatorOverIso (n : ℕ) :
    ((A.exteriorAnnihilator n).over U).toSheafOfModules ≅
      (B.exteriorAnnihilator n).toSheafOfModules where
  hom := exteriorAnnihilatorOverHom A U B n
  inv := exteriorAnnihilatorOverInv A U B n
  hom_inv_id := by
    refine (cancel_mono ((A.exteriorAnnihilator n).over U).ι).mp ?_
    refine Eq.trans ?_ (Category.id_comp ((A.exteriorAnnihilator n).over U).ι).symm
    refine (Category.assoc (exteriorAnnihilatorOverHom A U B n)
      (exteriorAnnihilatorOverInv A U B n) ((A.exteriorAnnihilator n).over U).ι).trans ?_
    refine Eq.trans (congrArg (fun z => exteriorAnnihilatorOverHom A U B n ≫ z)
      (exteriorAnnihilatorOverInv_ι A U B n)) ?_
    refine (Category.assoc (exteriorAnnihilatorOverHom A U B n) (B.exteriorAnnihilator n).ι
      (exteriorOverPieceIso A U B (n : ℤ)).inv).symm.trans ?_
    refine Eq.trans (congrArg (fun z => z ≫ (exteriorOverPieceIso A U B (n : ℤ)).inv)
      (exteriorAnnihilatorOverHom_ι A U B n)) ?_
    refine (Category.assoc ((A.exteriorAnnihilator n).over U).ι
      (exteriorOverPieceIso A U B (n : ℤ)).hom
      (exteriorOverPieceIso A U B (n : ℤ)).inv).trans ?_
    refine Eq.trans (congrArg (fun z => ((A.exteriorAnnihilator n).over U).ι ≫ z)
      (exteriorOverPieceIso A U B (n : ℤ)).hom_inv_id) ?_
    exact Category.comp_id _
  inv_hom_id := by
    refine (cancel_mono (B.exteriorAnnihilator n).ι).mp ?_
    refine Eq.trans ?_ (Category.id_comp (B.exteriorAnnihilator n).ι).symm
    refine (Category.assoc (exteriorAnnihilatorOverInv A U B n)
      (exteriorAnnihilatorOverHom A U B n) (B.exteriorAnnihilator n).ι).trans ?_
    refine Eq.trans (congrArg (fun z => exteriorAnnihilatorOverInv A U B n ≫ z)
      (exteriorAnnihilatorOverHom_ι A U B n)) ?_
    refine (Category.assoc (exteriorAnnihilatorOverInv A U B n)
      ((A.exteriorAnnihilator n).over U).ι
      (exteriorOverPieceIso A U B (n : ℤ)).hom).symm.trans ?_
    refine Eq.trans (congrArg (fun z => z ≫ (exteriorOverPieceIso A U B (n : ℤ)).hom)
      (exteriorAnnihilatorOverInv_ι A U B n)) ?_
    refine (Category.assoc (B.exteriorAnnihilator n).ι
      (exteriorOverPieceIso A U B (n : ℤ)).inv
      (exteriorOverPieceIso A U B (n : ℤ)).hom).trans ?_
    refine Eq.trans (congrArg (fun z => (B.exteriorAnnihilator n).ι ≫ z)
      (exteriorOverPieceIso A U B (n : ℤ)).inv_hom_id) ?_
    exact Category.comp_id _

variable [Limits.HasBinaryProducts C]

/-- **The determinant of `A` restricted to the slice site over `U` is the determinant of `B`.**
Restriction preserves the `ℕ`-indexed coproduct, being a left adjoint, and the summands are
compared degreewise by `exteriorAnnihilatorOverIso`. -/
def determinantOverIso : A.determinant.over U ≅ B.determinant :=
  letI : (SheafOfModules.overFunctor.{w} (toRingCat J Osharp) U).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward.{w}
      (𝟙 ((toRingCat J Osharp).over U))).IsLeftAdjoint
  letI : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{w} (toRingCat J Osharp) U) :=
    (Adjunction.ofIsLeftAdjoint
      (SheafOfModules.overFunctor.{w} (toRingCat J Osharp) U)).leftAdjoint_preservesColimits
  PreservesCoproduct.iso (SheafOfModules.overFunctor.{w} (toRingCat J Osharp) U)
      (fun n : ℕ => (A.exteriorAnnihilator n).toSheafOfModules) ≪≫
    Sigma.mapIso fun n : ℕ => exteriorAnnihilatorOverIso A U B n

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
