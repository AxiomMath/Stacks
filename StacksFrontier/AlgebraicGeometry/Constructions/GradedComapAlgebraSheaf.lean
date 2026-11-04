module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineAlgebraHom

/-!
# A degreewise comparison of graded algebra sheaves, and the morphism out of the algebra pullback

Let `g : Z ⟶ Y` be a morphism of schemes with `Y` **affine**, let `𝓐` be a sheaf of graded
`𝒪_Y`-algebras and `𝓒` a sheaf of graded `𝒪_Z`-algebras, both with commutative homogeneous
multiplication. A **degreewise comparison** is a family of morphisms of sheaves of modules

`φ n : 𝓐ₙ ⟶ g_*(𝓒ₙ)`

carrying products of homogeneous sections to products and the degree-zero unit to the unit. This
file assembles such a family into a morphism of sheaves of commutative algebras

`β : ⨁ₙ 𝓐ₙ ⟶ g_*(⨁ₙ 𝓒ₙ)`

and transposes it across the base-change adjunction for algebra sheaves into

`ψ : (algebraPullback g).obj (⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ 𝓒ₙ`,

the datum a relative spectrum over `Z` consumes and the one [Stacks, Tag 01LX] part (2)
produces. It also provides the tools with which `ψ` is shown **locally surjective**: the image
subring of `ψ` on the sections over an open, its stability under restriction and under the
structure map, and the reduction of local surjectivity to the single statement that every
*homogeneous* section of `𝓒ₙ` over an affine open of `Z` lies in that subring.

## Why this is general and where it was not

Exactly this chain existed, for the Rees algebra `⨁ₙ Kⁿ` of a quasi-coherent sheaf of ideals `K`
on `Y` and the Rees algebra of its inverse image, in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/ReesComapAlgebraSheaf.lean` and
`StacksFrontier/AlgebraicGeometry/FormalFunctions/ReesComapLocallySurjective.lean`. Nothing in the assembly uses the Rees algebra: the ideal
sheaf enters only in the degreewise comparison `Stacks.Blowup.reesPieceComap` of
[Stacks, Tag 01OG], which is the `φ` above, and in the last step of local surjectivity, which is
a statement about ambient sections of the pieces. Those two remain there; everything between
them is here, and the Rees declarations are now instantiations of the ones below.

## Main definitions

* `Stacks.GradedComap.PieceComparison`: the degreewise comparison, with its two laws.
* `Stacks.GradedComap.totalHom`: **a degreewise comparison on the sections over an open `V` of
  `Y`**, as a ring homomorphism `⨁ₙ Γ(V, 𝓐ₙ) →+* Γ(g⁻¹V, ⨁ₙ 𝓒ₙ)`. No affineness is used.
* `Stacks.GradedComap.sections` and `Stacks.GradedComap.algebraHom`: **`β`**, for `Y` affine.
* `Stacks.GradedComap.pullbackHom`: **`ψ`, its adjoint transpose.**
* `Stacks.GradedComap.image`: the image of `ψ` on the sections over an open, as a subring.

## Main results

* `Stacks.GradedComap.totalHom_incl`: the assembled ring homomorphism on a homogeneous section is
  `φ n` followed by the degree-`n` inclusion into the ungraded realization. This is the only
  description of it there is.
* `Stacks.GradedComap.totalHom_structureMap`: the compatibility with the two structure maps,
  which is what makes `β` a morphism of *algebra* sheaves and not merely of sheaves of rings. It
  is **not** an extra hypothesis on `φ`: `φ 0` is a morphism of sheaves of `𝒪_Y`-modules, so it
  is `𝒪_Y`-linear, and the compatibility is that linearity at the unit
  (`Stacks.GradedComap.app_smul_one`).
* `Stacks.GradedComap.pullbackHom_app_unit`: **the only handle on `ψ`** — on the unit image of a
  global section of `⨁ₙ 𝓐ₙ` it is `β` on that section.
* `Stacks.GradedComap.isLocallySurjective_pullbackHom`: **`ψ` is locally surjective** as soon as
  every homogeneous section of every `𝓒ₙ` over every affine open of `Z` lies in the image of `ψ`.
* `Stacks.GradedComap.mem_image_ungradedIncl_zero`, `mem_image_ungradedIncl_add` and
  `mem_image_ungradedIncl_smul`: the homogeneous sections whose inclusion lies in the image of
  `ψ` form a `Γ(Z, V)`-submodule — which is what reduces that hypothesis to a generation
  statement.

## Implementation notes

The assembly on sections is `Stacks.GradedAlgebra.totalRingHomOfPieces`, stated at the level of
graded algebras of presheaves of modules on an arbitrary site rather than for a sheaf of graded
algebras on a scheme, and this is not for generality. On a scheme the ring sheaf arrives as
`X.ringCatSheaf : TopCat.Sheaf RingCat ↥X`, which is definitionally but not syntactically
`CategoryTheory.Sheaf (Opens.grothendieckTopology ↥X) RingCat`; a goal mentioning
`SheafOfModules.GradedAlgebra.ungradedSheaf` of it is then not type-correct at implicit
transparency, and every `rw` inside such a proof fails. Proving the assembly where no sheaf type
occurs, and instantiating it with `exact`-level applications that check at default transparency,
is what avoids that. For the same reason the computations below are written with `Eq.trans` and
`congrArg` rather than `rw`.

`Stacks.CommRingSheaf.ofRingCatHom` is used, rather than `CommRingCat.ofHom`, to produce the
morphism on global sections: the commutative ring structure on the sections of the ungraded
realization is `Stacks.CommRingSheaf.commRing`, which is not a global instance, so instance
search for `CommRing` on the carrier fails and `CommRingCat.ofHom` cannot elaborate.

`Stacks.GradedComap.pushforwardSection` is the identity map from the sections of `g_*(𝓒ₙ)` over
`V` to the sections of `𝓒ₙ` over `g⁻¹V`. The two types are the same up to unfolding the direct
image, so no statement *about a function application* needs it; but `•` does, because the scalar
action visible on the first spelling is the one of `Γ(Y, V)` through `g^♯` and instance search
does not unfold the direct image to find the action of `Γ(Z, g⁻¹V)`.

No `@[stacks]` attribute is attached: assembling a degreewise comparison is a step inside the
base change of [Stacks, Tag 0897], not a numbered result of the source.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe w v u

namespace Stacks.GradedComap

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (𝓐 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
  (𝓒 : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)

/-- The sections of `g_*(𝓒ₙ)` over `V`, read as sections of `𝓒ₙ` over `g⁻¹V`. The two types are
the same; naming the identification lets a statement mention the scalar action of
`Γ(Z, g⁻¹V)`. -/
def pushforwardSection (n : ℤ) (V : Y.Opens)
    (y : ((SheafOfModules.pushforward g.toRingCatSheafHom).obj (𝓒.piece n)).val.obj (op V)) :
    (𝓒.piece n).val.obj (op (g ⁻¹ᵁ V)) := y

/-- **A degreewise comparison of graded algebra sheaves along `g : Z ⟶ Y`**: a morphism
`𝓐ₙ ⟶ g_*(𝓒ₙ)` of sheaves of `𝒪_Y`-modules in each degree, multiplicative on homogeneous local
sections and carrying the degree-zero unit to the unit.

Compatibility with the structure maps from `𝒪_Y` is **not** a field: it follows from
`𝒪_Y`-linearity of the degree-zero component, which a morphism of sheaves of modules has by
definition (`Stacks.GradedComap.app_smul_one`). -/
structure PieceComparison where
  /-- The morphism of sheaves of `𝒪_Y`-modules in each degree. -/
  app (n : ℤ) : 𝓐.piece n ⟶ (SheafOfModules.pushforward g.toRingCatSheafHom).obj (𝓒.piece n)
  /-- Products of homogeneous local sections are preserved. -/
  map_mul (i j : ℤ) (V : Y.Opens) (x : (𝓐.piece i).val.obj (op V))
      (y : (𝓐.piece j).val.obj (op V)) :
    (app (i + j)).val.app (op V) ((𝓐.mul i j).app (op V) x y) =
      (𝓒.mul i j).app (op (g ⁻¹ᵁ V)) ((app i).val.app (op V) x) ((app j).val.app (op V) y)
  /-- The degree-zero unit is preserved. -/
  map_one (V : Y.Opens) :
    (app 0).val.app (op V) (𝓐.one.eval (op V)) = 𝓒.one.eval (op (g ⁻¹ᵁ V))

variable (D : PieceComparison g 𝓐 𝓒)

/-! ### The comparison on the sections over an open of the base -/

/-- The degree-`n` comparison `Γ(V, 𝓐ₙ) ⟶ Γ(g⁻¹V, ⨁ₙ 𝓒ₙ)`: the comparison on the homogeneous
piece followed by the degree-`n` inclusion into the ungraded realization, as an additive map. -/
def inclAddHom (n : ℤ) (V : Y.Opens) :
    (𝓐.piece n).val.obj (op V) →+ 𝓒.ungradedSheaf.obj.obj (op (g ⁻¹ᵁ V)) where
  toFun x := 𝓒.ungradedIncl n ((D.app n).val.app (op V) x)
  map_zero' := by
    rw [map_zero]
    exact Stacks.GradedAlgebra.inclSheaf_zero _ _ n
  map_add' x y := by
    rw [map_add]
    exact 𝓒.ungradedIncl_add n _ _ _

/-- **A degreewise comparison on the sections over an open `V` of the base**, as a ring
homomorphism `⨁ₙ Γ(V, 𝓐ₙ) →+* Γ(g⁻¹V, ⨁ₙ 𝓒ₙ)`.

The comparison is multiplicative and unital by its two laws, and the degree-`n` inclusions into
the ungraded realization carry the graded multiplication to the ring multiplication
(`SheafOfModules.GradedAlgebra.ungradedIncl_mul`), so
`Stacks.GradedAlgebra.totalRingHomOfPieces` applies. No affineness is used here. -/
def totalHom (V : Y.Opens) :
    𝓐.toPresheafGradedAlgebra.Total (op V) →+* 𝓒.ungradedSheaf.obj.obj (op (g ⁻¹ᵁ V)) :=
  Stacks.GradedAlgebra.totalRingHomOfPieces _ _ (fun n => inclAddHom g 𝓐 𝓒 D n V)
    ((congrArg (𝓒.ungradedIncl 0) (D.map_one V)).trans (𝓒.ungradedIncl_one _))
    fun i j x y =>
      (congrArg (𝓒.ungradedIncl (i + j)) (D.map_mul i j V x y)).trans
        (𝓒.ungradedIncl_mul i j _ _).symm

/-- **The only description of the comparison on sections**: on a homogeneous section it is `φ n`
followed by the degree-`n` inclusion. -/
theorem totalHom_incl (V : Y.Opens) (n : ℤ) (x : (𝓐.piece n).val.obj (op V)) :
    totalHom g 𝓐 𝓒 D V (𝓐.toPresheafGradedAlgebra.incl n x) =
      𝓒.ungradedIncl n ((D.app n).val.app (op V) x) :=
  DirectSum.toAddMonoid_of (fun n => inclAddHom g 𝓐 𝓒 D n V) n x

/-- **The comparison carries a scalar multiple of the unit to the corresponding scalar multiple of
the unit.** This is the `𝒪_Y`-linearity of the degree-zero component — a morphism of sheaves of
modules has it by definition — evaluated at the unit, and it is the degree-zero content of the
compatibility of the comparison with the structure maps. -/
theorem app_smul_one (V : Y.Opens) (r : Y.ringCatSheaf.obj.obj (op V)) :
    pushforwardSection g 𝓒 0 V ((D.app 0).val.app (op V) (r • 𝓐.one.eval (op V))) =
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from (g.app V).hom (show Γ(Y, V) from r)) •
        𝓒.one.eval (op (g ⁻¹ᵁ V)) :=
  (((D.app 0).val.app (op V)).hom.map_smul r (𝓐.one.eval (op V))).trans
    (congrArg (fun t : (𝓒.piece 0).val.obj (op (g ⁻¹ᵁ V)) =>
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from (g.app V).hom (show Γ(Y, V) from r)) • t)
      (D.map_one V))

/-- **The comparison on sections is compatible with the structure maps from the base ring.** The
structure map of the ungraded realization is `r ↦ r • 1`
(`Stacks.GradedAlgebra.structureMap`), so this is `Stacks.GradedComap.app_smul_one` read through
`SheafOfModules.GradedAlgebra.ungradedIncl_smul_one`. -/
theorem totalHom_structureMap (V : Y.Opens) (r : Y.ringCatSheaf.obj.obj (op V)) :
    totalHom g 𝓐 𝓒 D V (𝓐.toPresheafGradedAlgebra.structureMap (op V) r) =
      (𝓒.ungradedStructureMap.hom.app (op (g ⁻¹ᵁ V))).hom
        ((g.app V).hom (show Γ(Y, V) from r)) := by
  have h1 : 𝓐.toPresheafGradedAlgebra.structureMap (op V) r =
      𝓐.toPresheafGradedAlgebra.incl 0 (r • 𝓐.one.eval (op V)) :=
    (congrArg (fun t => r • t) (𝓐.toPresheafGradedAlgebra.one_eq_incl (op V))).trans
      (𝓐.toPresheafGradedAlgebra.incl_smul 0 r _).symm
  refine Eq.trans (congrArg (totalHom g 𝓐 𝓒 D V) h1) ?_
  refine Eq.trans (totalHom_incl g 𝓐 𝓒 D V 0 _) ?_
  refine Eq.trans (congrArg (𝓒.ungradedIncl 0) (app_smul_one g 𝓐 𝓒 D V r)) ?_
  exact 𝓒.ungradedIncl_smul_one _ _

/-! ### `β` and `ψ` over an affine base -/

section Affine

variable (hA : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝓐.piece i).val.obj W)
    (b : (𝓐.piece j).val.obj W), HEq ((𝓐.mul i j).app W a b) ((𝓐.mul j i).app W b a))
  (hC : ∀ (i j : ℤ) (W : (Opens ↥Z)ᵒᵖ) (a : (𝓒.piece i).val.obj W)
    (b : (𝓒.piece j).val.obj W), HEq ((𝓒.mul i j).app W a b) ((𝓒.mul j i).app W b a))
  [IsAffine Y]

/-- The comparison on *global* sections over an affine base, as a morphism of rings: the global
sections of `⨁ₙ 𝓐ₙ` are the direct sum `⨁ₙ Γ(Y, 𝓐ₙ)` because `Y` is affine
(`Stacks.RelativeSpec.totalSectionsRingEquiv`), and `Stacks.GradedComap.totalHom` is applied to
that. -/
def sectionsRingCatHom :
    𝓐.ungradedSheaf.obj.obj (op (⊤ : Y.Opens)) ⟶
      𝓒.ungradedSheaf.obj.obj (op (g ⁻¹ᵁ (⊤ : Y.Opens))) :=
  RingCat.ofHom
    ((totalHom g 𝓐 𝓒 D ⊤).comp
      (Stacks.RelativeSpec.totalSectionsRingEquiv Y 𝓐 hA (isAffineOpen_top Y)).symm.toRingHom)

/-- The comparison on global sections, as a morphism of *commutative* rings, i.e. in the form the
universal property of an algebra sheaf over an affine base consumes. The sections of the
ungraded realization commute (`SheafOfModules.GradedAlgebra.mul_comm_ungradedSheaf`) and the
carrier and the operations are unchanged, so this is the same data as
`Stacks.GradedComap.sectionsRingCatHom`. -/
def sections :
    AlgebraSheaf.sections (gradedAlgebraSheaf Y 𝓐 hA) ⊤ ⟶
      AlgebraSheaf.sections ((algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC)) ⊤ :=
  Stacks.CommRingSheaf.ofRingCatHom
    (𝓐.mul_comm_ungradedSheaf hA (op (⊤ : Y.Opens)))
    (𝓒.mul_comm_ungradedSheaf hC (op (g ⁻¹ᵁ (⊤ : Y.Opens))))
    (sectionsRingCatHom g 𝓐 𝓒 D hA)

/-- `totalHom` on the top open only sees the direct-sum section, not the way it is read through
the identification with the global sections of `⨁ₙ 𝓐ₙ`. -/
private theorem totalHom_symm_totalSectionsRingEquiv
    (x : 𝓐.toPresheafGradedAlgebra.Total (op (⊤ : Y.Opens))) :
    totalHom g 𝓐 𝓒 D ⊤
        ((Stacks.RelativeSpec.totalSectionsRingEquiv Y 𝓐 hA (isAffineOpen_top Y)).symm
          (Stacks.RelativeSpec.totalSectionsRingEquiv Y 𝓐 hA (isAffineOpen_top Y) x)) =
      totalHom g 𝓐 𝓒 D ⊤ x :=
  congrArg _ (Equiv.symm_apply_apply _ _)

/-- **The comparison on global sections is compatible with the two structure maps**, which is what
makes it a morphism of algebra sheaves rather than merely of sheaves of rings. The identification
of the global sections with the direct sum is `Stacks.RelativeSpec.totalSectionsRingEquiv`, which
is the unit of the sheafification, so the structure map of `⨁ₙ 𝓐ₙ` corresponds to the structure
map `r ↦ r • 1` of the presheaf direct sum; and there
`Stacks.GradedComap.totalHom_structureMap` is the statement. -/
theorem sections_unitTop :
    (gradedAlgebraSheaf Y 𝓐 hA).unitTop ≫ sections g 𝓐 𝓒 D hA hC =
      ((algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC)).unitTop := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  exact (totalHom_symm_totalSectionsRingEquiv g 𝓐 𝓒 D hA
    (𝓐.toPresheafGradedAlgebra.structureMap (op ⊤) r)).trans
      (totalHom_structureMap g 𝓐 𝓒 D ⊤ r)

variable [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]

/-- **`β : ⨁ₙ 𝓐ₙ ⟶ g_*(⨁ₙ 𝓒ₙ)`, a degreewise comparison as a morphism of sheaves of commutative
`𝒪_Y`-algebras**, for a morphism `g : Z ⟶ Y` into an affine base.

`⨁ₙ 𝓐ₙ` is quasi-coherent as an algebra sheaf and `Y` is affine, so a morphism out of it is
exactly a ring homomorphism on global sections compatible with the two structure maps
(`Stacks.RelativeSpec.AlgebraSheaf.algebraHom`); that homomorphism is
`Stacks.GradedComap.sections` and the compatibility is
`Stacks.GradedComap.sections_unitTop`. -/
def algebraHom :
    gradedAlgebraSheaf Y 𝓐 hA ⟶ (algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC) :=
  AlgebraSheaf.algebraHom _ _ (sections_unitTop g 𝓐 𝓒 D hA hC)

/-- **`ψ : g^*(⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ 𝓒ₙ`, the adjoint transpose of `β`**, where `g^*` is the *algebra*
pullback `g⁻¹(−) ⊗_{g⁻¹𝒪_Y} 𝒪_Z` — the pullback a relative spectrum over `Z` consumes and the one
[Stacks, Tag 01LX] part (2) produces, not a degreewise module pullback. -/
def pullbackHom :
    (algebraPullback g).obj (gradedAlgebraSheaf Y 𝓐 hA) ⟶ gradedAlgebraSheaf Z 𝓒 hC :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm (algebraHom g 𝓐 𝓒 D hA hC)

/-- `β` on global sections is `Stacks.GradedComap.sections`, which is the universal property of an
algebra sheaf over an affine base read back. -/
theorem algebraHom_right_app_top :
    (algebraHom g 𝓐 𝓒 D hA hC).right.hom.app (op ⊤) = sections g 𝓐 𝓒 D hA hC :=
  AlgebraSheaf.algebraHom_right_app_top (gradedAlgebraSheaf Y 𝓐 hA)
    ((algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC)) (sections_unitTop g 𝓐 𝓒 D hA hC)

/-- **The adjunction identity defining `ψ`**: the unit of the base-change adjunction for algebra
sheaves followed by the pushforward of `ψ` is `β`. -/
theorem unit_comp_map_pullbackHom :
    (algebraPullbackPushforwardAdjunction g).unit.app (gradedAlgebraSheaf Y 𝓐 hA) ≫
        (algebraPushforward g).map (pullbackHom g 𝓐 𝓒 D hA hC) =
      algebraHom g 𝓐 𝓒 D hA hC :=
  (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g) (gradedAlgebraSheaf Y 𝓐 hA)
      (gradedAlgebraSheaf Z 𝓒 hC) (pullbackHom g 𝓐 𝓒 D hA hC)).symm.trans
    (Equiv.apply_symm_apply
      ((algebraPullbackPushforwardAdjunction g).homEquiv (gradedAlgebraSheaf Y 𝓐 hA)
        (gradedAlgebraSheaf Z 𝓒 hC)) _)

/-- **`ψ` on the unit image of a global section of `⨁ₙ 𝓐ₙ` is `β` on that section.** This is the
only handle on `ψ` there is, and it is the entry point for its local surjectivity. -/
theorem pullbackHom_app_unit (b : AlgebraSheaf.sections (gradedAlgebraSheaf Y 𝓐 hA) ⊤) :
    (pullbackHom g 𝓐 𝓒 D hA hC).right.hom.app (op (g ⁻¹ᵁ (⊤ : Y.Opens)))
        (((algebraPullbackPushforwardAdjunction g).unit.app
          (gradedAlgebraSheaf Y 𝓐 hA)).right.hom.app (op ⊤) b) =
      sections g 𝓐 𝓒 D hA hC b := by
  refine Eq.trans (show _ = (ConcreteCategory.hom
      ((((algebraPullbackPushforwardAdjunction g).unit.app (gradedAlgebraSheaf Y 𝓐 hA) ≫
        (algebraPushforward g).map (pullbackHom g 𝓐 𝓒 D hA hC)).right).hom.app (op ⊤))) b
      from rfl) ?_
  refine Eq.trans (congrArg (fun t : gradedAlgebraSheaf Y 𝓐 hA ⟶
      (algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC) =>
    (ConcreteCategory.hom (t.right.hom.app (op ⊤))) b)
    (unit_comp_map_pullbackHom g 𝓐 𝓒 D hA hC)) ?_
  exact congrArg (fun φ : AlgebraSheaf.sections (gradedAlgebraSheaf Y 𝓐 hA) ⊤ ⟶
      AlgebraSheaf.sections ((algebraPushforward g).obj (gradedAlgebraSheaf Z 𝓒 hC)) ⊤ =>
    ConcreteCategory.hom φ b) (algebraHom_right_app_top g 𝓐 𝓒 D hA hC)

omit [(gradedAlgebraSheaf Y 𝓐 hA).IsQuasicoherent] in
/-- `β` on a global homogeneous section is the degree-`n` inclusion of the comparison's value on
it. -/
theorem sections_ungradedIncl (n : ℤ) (x : (𝓐.piece n).val.obj (op (⊤ : Y.Opens))) :
    sections g 𝓐 𝓒 D hA hC (𝓐.ungradedIncl n x) =
      𝓒.ungradedIncl n ((D.app n).val.app (op ⊤) x) := by
  exact (totalHom_symm_totalSectionsRingEquiv g 𝓐 𝓒 D hA
    (𝓐.toPresheafGradedAlgebra.incl n x)).trans (totalHom_incl g 𝓐 𝓒 D ⊤ n x)

/-! ### Local surjectivity of `ψ` -/

/-- The image of `ψ` on the sections over an open, as a subring of the sections of `⨁ₙ 𝓒ₙ`. -/
def image (V : Z.Opens) :
    Subring ↥(AlgebraSheaf.sections (gradedAlgebraSheaf Z 𝓒 hC) V) :=
  RingHom.range ((pullbackHom g 𝓐 𝓒 D hA hC).right.hom.app (op V)).hom

/-- Transport membership in the image of `ψ` along an equality of sections. -/
theorem mem_image_congr {V : Z.Opens} {a b : 𝓒.ungradedSheaf.obj.obj (op V)} (h : a = b)
    (ha : a ∈ image g 𝓐 𝓒 D hA hC V) : b ∈ image g 𝓐 𝓒 D hA hC V := h ▸ ha

/-- The image of `ψ` contains the image of the structure map of `⨁ₙ 𝓒ₙ`, hence is a
`Γ(Z, V)`-submodule. This is nothing but `CategoryTheory.Under.w` for `ψ`. -/
theorem mem_image_structureMap (V : Z.Opens) (r : Z.ringCatSheaf.obj.obj (op V)) :
    (𝓒.ungradedStructureMap.hom.app (op V)).hom r ∈ image g 𝓐 𝓒 D hA hC V := by
  refine ⟨ConcreteCategory.hom
      (((algebraPullback g).obj (gradedAlgebraSheaf Y 𝓐 hA)).hom.hom.app (op V)) r, ?_⟩
  exact congrArg (fun φ : Z.sheaf ⟶ (gradedAlgebraSheaf Z 𝓒 hC).right =>
      ConcreteCategory.hom (φ.hom.app (op V)) r) (Under.w (pullbackHom g 𝓐 𝓒 D hA hC))

/-- **A global homogeneous section of `⨁ₙ 𝓐ₙ` is carried by `ψ` into the image over `g⁻¹⊤`.**
This is `Stacks.GradedComap.pullbackHom_app_unit` read through
`Stacks.GradedComap.sections_ungradedIncl`. -/
theorem mem_image_app (n : ℤ) (x : (𝓐.piece n).val.obj (op (⊤ : Y.Opens))) :
    𝓒.ungradedIncl n ((D.app n).val.app (op ⊤) x) ∈
      image g 𝓐 𝓒 D hA hC (g ⁻¹ᵁ (⊤ : Y.Opens)) :=
  ⟨_, (pullbackHom_app_unit g 𝓐 𝓒 D hA hC (𝓐.ungradedIncl n x)).trans
    (sections_ungradedIncl g 𝓐 𝓒 D hA hC n x)⟩

/-- The image of `ψ` is compatible with restriction: the restriction of a section in the image
over an open is in the image over any smaller open. -/
theorem mem_image_of_le {V W : Z.Opens} (h : V ≤ W)
    {t : ↥(AlgebraSheaf.sections (gradedAlgebraSheaf Z 𝓒 hC) W)}
    (ht : t ∈ image g 𝓐 𝓒 D hA hC W) :
    ConcreteCategory.hom ((gradedAlgebraSheaf Z 𝓒 hC).right.obj.map (homOfLE h).op) t ∈
      image g 𝓐 𝓒 D hA hC V := by
  obtain ⟨u, hu⟩ := ht
  refine ⟨ConcreteCategory.hom
    (((algebraPullback g).obj (gradedAlgebraSheaf Y 𝓐 hA)).right.obj.map (homOfLE h).op) u, ?_⟩
  refine Eq.trans
    (NatTrans.naturality_apply (pullbackHom g 𝓐 𝓒 D hA hC).right.hom (homOfLE h).op u) ?_
  exact congrArg (fun z => ConcreteCategory.hom
    ((gradedAlgebraSheaf Z 𝓒 hC).right.obj.map (homOfLE h).op) z) hu

/-- **The restriction to a smaller open of a global homogeneous section's image is in the image.**
`Stacks.GradedComap.mem_image_app` read through the naturality of the degree-`n` inclusion into
the ungraded realization. -/
theorem mem_image_app_restrict {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) (n : ℤ)
    (x : (𝓐.piece n).val.obj (op (⊤ : Y.Opens))) :
    𝓒.ungradedIncl n
        (Stacks.sectionRestrict (𝓒.piece n).val (homOfLE hV).op
          ((D.app n).val.app (op ⊤) x)) ∈
      image g 𝓐 𝓒 D hA hC V := by
  obtain ⟨u, hu⟩ := mem_image_of_le g 𝓐 𝓒 D hA hC hV (mem_image_app g 𝓐 𝓒 D hA hC n x)
  exact ⟨u, hu.trans (𝓒.ungradedIncl_naturality (homOfLE hV).op n
    ((D.app n).val.app (op ⊤) x))⟩

/-- The inclusion of the zero homogeneous section is in the image of `ψ`. -/
theorem mem_image_ungradedIncl_zero (n : ℤ) (V : Z.Opens) :
    𝓒.ungradedIncl n (0 : (𝓒.piece n).val.obj (op V)) ∈ image g 𝓐 𝓒 D hA hC V :=
  mem_image_congr g 𝓐 𝓒 D hA hC
    (Stacks.GradedAlgebra.inclSheaf_zero 𝓒.toPresheafGradedAlgebra _ n).symm
    (image g 𝓐 𝓒 D hA hC V).zero_mem

/-- The image of `ψ` is closed under sums of homogeneous sections. -/
theorem mem_image_ungradedIncl_add (n : ℤ) (V : Z.Opens)
    {x y : (𝓒.piece n).val.obj (op V)}
    (hx : 𝓒.ungradedIncl n x ∈ image g 𝓐 𝓒 D hA hC V)
    (hy : 𝓒.ungradedIncl n y ∈ image g 𝓐 𝓒 D hA hC V) :
    𝓒.ungradedIncl n (x + y) ∈ image g 𝓐 𝓒 D hA hC V :=
  mem_image_congr g 𝓐 𝓒 D hA hC (𝓒.ungradedIncl_add n (op V) x y).symm
    ((image g 𝓐 𝓒 D hA hC V).add_mem hx hy)

/-- **The image of `ψ` is a `Γ(Z, V)`-submodule of the homogeneous sections**, in the sense that
it is closed under scalar multiplication: it contains the image of the structure map
(`Stacks.GradedComap.mem_image_structureMap`) and is a subring. -/
theorem mem_image_ungradedIncl_smul (n : ℤ) (V : Z.Opens)
    (r : Z.ringCatSheaf.obj.obj (op V)) {x : (𝓒.piece n).val.obj (op V)}
    (hx : 𝓒.ungradedIncl n x ∈ image g 𝓐 𝓒 D hA hC V) :
    𝓒.ungradedIncl n (r • x) ∈ image g 𝓐 𝓒 D hA hC V :=
  mem_image_congr g 𝓐 𝓒 D hA hC (𝓒.ungradedIncl_smul n (op V) r x).symm
    ((image g 𝓐 𝓒 D hA hC V).mul_mem (mem_image_structureMap g 𝓐 𝓒 D hA hC V r) hx)

/-- **Every section of the direct sum of the homogeneous sections over an affine open is in the
image of `ψ`**, as soon as every homogeneous one is: a section of the presheaf direct sum is a
*finite* sum of homogeneous ones (`Stacks.GradedAlgebra.incl_induction`) and the image is a
subring. -/
theorem mem_image_totalUnit
    (hhom : ∀ {V : Z.Opens}, IsAffineOpen V → ∀ (n : ℤ) (x : (𝓒.piece n).val.obj (op V)),
      𝓒.ungradedIncl n x ∈ image g 𝓐 𝓒 D hA hC V)
    {V : Z.Opens} (hV : IsAffineOpen V) (a : 𝓒.toPresheafGradedAlgebra.Total (op V)) :
    𝓒.toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (Z : TopCat)) (op V) a ∈ image g 𝓐 𝓒 D hA hC V := by
  induction a using 𝓒.toPresheafGradedAlgebra.incl_induction with
  | zero => exact mem_image_congr g 𝓐 𝓒 D hA hC (map_zero _).symm (image g 𝓐 𝓒 D hA hC V).zero_mem
  | incl n x => exact hhom hV n x
  | add a a' ha ha' =>
      exact mem_image_congr g 𝓐 𝓒 D hA hC (map_add _ a a').symm
        ((image g 𝓐 𝓒 D hA hC V).add_mem ha ha')

/-- **`ψ` is surjective on the sections over an affine open** as soon as every homogeneous section
there is in its image. Over an affine open the sections of `⨁ₙ 𝓒ₙ` are the direct sum of the
sections of the homogeneous pieces (`Stacks.RelativeSpec.totalSectionsRingEquiv`). -/
theorem surjective_pullbackHom_right_app_of_isAffineOpen
    (hhom : ∀ {V : Z.Opens}, IsAffineOpen V → ∀ (n : ℤ) (x : (𝓒.piece n).val.obj (op V)),
      𝓒.ungradedIncl n x ∈ image g 𝓐 𝓒 D hA hC V)
    {V : Z.Opens} (hV : IsAffineOpen V) :
    Function.Surjective
      (ConcreteCategory.hom ((pullbackHom g 𝓐 𝓒 D hA hC).right.hom.app (op V))) := by
  intro s
  refine RingHom.mem_range.mp ?_
  refine Eq.mp (congrArg (fun z => z ∈ image g 𝓐 𝓒 D hA hC V) ?_)
    (mem_image_totalUnit g 𝓐 𝓒 D hA hC hhom hV
      ((Stacks.RelativeSpec.totalSectionsRingEquiv Z 𝓒 hC hV).symm s))
  exact (Stacks.RelativeSpec.totalSectionsRingEquiv Z 𝓒 hC hV).apply_symm_apply s

/-- **`ψ : g^*(⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ 𝓒ₙ` is locally surjective** as soon as every homogeneous section of
every piece over every affine open of `Z` is in its image: the affine opens below an open generate
a covering sieve of it (`AlgebraicGeometry.generate_affineOpensPresieve_mem`). -/
theorem isLocallySurjective_pullbackHom
    (hhom : ∀ {V : Z.Opens}, IsAffineOpen V → ∀ (n : ℤ) (x : (𝓒.piece n).val.obj (op V)),
      𝓒.ungradedIncl n x ∈ image g 𝓐 𝓒 D hA hC V) :
    CategoryTheory.Sheaf.IsLocallySurjective (pullbackHom g 𝓐 𝓒 D hA hC).right := by
  refine ⟨fun {W} s => ?_⟩
  refine (Opens.grothendieckTopology (Z : TopCat)).superset_covering
      ((Sieve.generate_le_iff _ _).2 ?_) (generate_affineOpensPresieve_mem Z W)
  intro V i hV
  exact surjective_pullbackHom_right_app_of_isAffineOpen g 𝓐 𝓒 D hA hC hhom hV
    (ConcreteCategory.hom ((gradedAlgebraSheaf Z 𝓒 hC).right.obj.map i.op) s)

end Affine

end Stacks.GradedComap

end
