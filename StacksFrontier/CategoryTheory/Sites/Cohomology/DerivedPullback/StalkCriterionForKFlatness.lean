module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Homology.TotalComplexTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk criterion for K-flatness on a ringed site

Let `(C, O)` be a ringed site and `K` a cochain complex of `O`-modules. If `C` has enough
points and the complex `K_Φ` of modules over the stalk `O_Φ` is K-flat for every point `Φ`,
then `K` is K-flat. This is part (2) of Stacks 0DEN.

## Main definitions

* `Stacks.Sheaves.KFlatStalkCriterion.stalkComplex`: the complex of modules over the stalk of `O`
  obtained by taking
  stalks degreewise.
* `Stacks.Sheaves.KFlatStalkCriterion.StalkTensorData`: the datum of Stacks 03EL at one point of
  the site — the
  stalk of a tensor product of sheaves of modules is the tensor product of the stalks over the
  stalk ring — together with its two naturality squares.

## Main results

* `Stacks.Sheaves.KFlatStalkCriterion.totalStalkIso`: the stalk of a total tensor complex is the
  total tensor
  complex of the stalks.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlat_of_stalks`: part (2) of the source, K-flatness detected
  at the stalks.

## Implementation notes

The source's proof of part (2) is one sentence: "`⊗` and direct sums commute with taking
stalks, and we can check exactness at stalks". The three inputs are separated here, and two of
the three are proved rather than assumed:

* *exactness checked at stalks* is
  `Stacks.acyclic_iff_forall_acyclic_sheafModuleFiberOfCommRing`, the module-valued form of
  Stacks 05V3 at the generality of a site;
* *direct sums commute with taking stalks* is
  `Stacks.preservesColimits_sheafModuleFiberOfCommRing`, which is what lets the total complex
  pass through the stalk functor;
* *`⊗` commutes with taking stalks* is Stacks 03EL, and it is the one input assumed, as
  `StalkTensorData`. Nothing weaker suffices: it is the only statement in the chain that is
  about the tensor product of sheaves of modules rather than about colimits or exactness, and
  it is not in the tree in any form at site generality (the ringed-space analogue is
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`).

Part (1) of the source — a K-flat complex has K-flat stalks — is *not* in this file. Its proof
reduces, through the resolution of Stacks 06YS and two-out-of-three in the mapping-cone
triangle, to the case of a complex that is simultaneously acyclic and K-flat, and that case
runs through Stacks 0E8F (available, as
`CochainComplex.kFlat_of_tensor_finitelyPresented_acyclic`) together with the realization of a
finitely presented module over the stalk ring as the stalk of a sheaf of modules — which is
Stacks 05N7 (available) followed by Stacks 0E8K, restriction of a K-flat complex to a
localization of the site, of which there is nothing in the tree. No declaration here carries
the 0DEN tag, since neither part is proved under the source's own hypotheses: `kFlat_of_stalks`
carries `StalkTensorData` in addition to them.

`StalkTensorData` is a structure with three fields rather than a natural isomorphism of
curried bifunctors, because that is the shape
`CategoryTheory.Functor.mapBifunctorTotalIso` consumes: a family of isomorphisms indexed by
pairs of objects together with naturality in each variable separately. A producer of Stacks
03EL has exactly that, and packaging it as one `NatIso` between composites of whiskering
functors would have to be unpackaged again.

The hypotheses are `HasWeakSheafify` rather than `HasSheafify`, as the Stacks statement assumes:
`HasSheafify J AddCommGrpCat` follows from `HasWeakSheafify` together with
`J.WEqualsLocallyBijective AddCommGrpCat` by
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`, and is introduced inside
the proof where the exactness results need it. Assuming it in the statement would strengthen
the hypothesis and so weaken the theorem.

K-flatness on the stalk side is `CochainComplex.KFlat.{u, u}` (Stacks 06XZ), whose monoidal
product of complexes is definitionally the total complex of the bifunctor
`MonoidalCategory.curriedTensor (ModuleCat.{u} O_Φ)` — which is the spelling used throughout
here, and which `CochainComplex.kFlat_iff_kFlatBifunctor` records.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Sheaves.KFlatStalkCriterion

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The stalk of the structure sheaf of a ringed site at a point of the site, as a commutative
ring. -/
noncomputable abbrev structureStalk (Φ : J.Point.{u}) : CommRingCat.{u} :=
  (Φ.presheafFiber (A := CommRingCat.{u})).obj O.obj

/-- **The stalk complex.** Taking stalks at a point `Φ` of the site in each degree carries a
cochain complex of sheaves of `O`-modules to a cochain complex of modules over the stalk
`O_Φ`. This is `K_Φ` in the statement of the source. -/
noncomputable abbrev stalkComplex (Φ : J.Point.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    CochainComplex (ModuleCat.{u} (structureStalk O Φ)) ℤ :=
  ((Stacks.sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- **Stacks 03EL at one point of the site.** The stalk at `Φ` of the tensor product of two
sheaves of `O`-modules is the tensor product of their stalks over the stalk ring `O_Φ`, and
the identification is natural in each variable.

This is the one input to the stalk criterion for K-flatness that is not proved in this
development; see the implementation notes. The two naturality fields are stated in the shape
`CategoryTheory.Functor.mapBifunctorTotalIso` consumes. -/
structure StalkTensorData (Φ : J.Point.{u}) where
  /-- The stalk of a tensor product is the tensor product of the stalks. -/
  iso : ∀ A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O),
    (Stacks.sheafModuleFiberOfCommRing Φ O).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B) ≅
      ((curriedTensor (ModuleCat.{u} (structureStalk O Φ))).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ O).obj A)).obj
        ((Stacks.sheafModuleFiberOfCommRing Φ O).obj B)
  /-- The identification is natural in the left-hand variable. -/
  naturality_left : ∀ {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A
    ⟶ A')
      (B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)),
    (Stacks.sheafModuleFiberOfCommRing Φ O).map (((Stacks.SheafOfModules.Tensor.sheafTensor O).map
      f).app B) ≫
        (iso A' B).hom =
      (iso A B).hom ≫ ((curriedTensor (ModuleCat.{u} (structureStalk O Φ))).map
        ((Stacks.sheafModuleFiberOfCommRing Φ O).map f)).app
          ((Stacks.sheafModuleFiberOfCommRing Φ O).obj B)
  /-- The identification is natural in the right-hand variable. -/
  naturality_right : ∀ (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      {B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (g : B ⟶ B'),
    (Stacks.sheafModuleFiberOfCommRing Φ O).map (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj
      A).map g) ≫
        (iso A B').hom =
      (iso A B).hom ≫ ((curriedTensor (ModuleCat.{u} (structureStalk O Φ))).obj
        ((Stacks.sheafModuleFiberOfCommRing Φ O).obj A)).map
          ((Stacks.sheafModuleFiberOfCommRing Φ O).map g)

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The total tensor complex of Stacks 06YM is the total complex of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, by definition. Hoisted into its own equation because
  the two
spellings sit on either side of a project `def` and a tactic will not unfold across it. -/
theorem tensorComplex_obj_obj
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex O).obj A).obj B =
      HomologicalComplex.mapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor O)
        (ComplexShape.up ℤ) :=
  rfl

/-- **The stalk of a total tensor complex is the total tensor complex of the stalks.** This is
Stacks 03EL carried through totalisation: the degree-`n` term of a total complex is a direct
sum over an antidiagonal, and the stalk functor commutes with those direct sums by
`Stacks.preservesColimits_sheafModuleFiberOfCommRing`. -/
noncomputable def totalStalkIso (Φ : J.Point.{u}) (D : StalkTensorData O Φ)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor O)
          (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor (stalkComplex O Φ A) (stalkComplex O Φ B)
        (curriedTensor (ModuleCat.{u} (structureStalk O Φ))) (ComplexShape.up ℤ) := by
  letI : (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      ModuleCat.{u} (structureStalk O Φ) from Stacks.sheafModuleFiberOfCommRing Φ O).Additive :=
    Stacks.additive_sheafModuleFiberOfCommRing Φ O
  letI : PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
        ModuleCat.{u} (structureStalk O Φ) from Stacks.sheafModuleFiberOfCommRing Φ O) :=
    Stacks.preservesColimits_sheafModuleFiberOfCommRing Φ O
  letI : ∀ degree : ℤ, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {degree}))
      (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
        ModuleCat.{u} (structureStalk O Φ) from Stacks.sheafModuleFiberOfCommRing Φ O) :=
    fun degree => inferInstance
  -- The three data of `D` are supplied one at a time rather than inline: with `D.iso` written
  -- as an argument, checking its type against the expected one runs the elaborator's `whnf`
  -- past its budget, while against a goal the same check is immediate.
  refine Functor.mapBifunctorTotalIso (Stacks.SheafOfModules.Tensor.sheafTensor O)
    (curriedTensor (ModuleCat.{u} (structureStalk O Φ)))
    (Stacks.sheafModuleFiberOfCommRing Φ O) (Stacks.sheafModuleFiberOfCommRing Φ O)
    (Stacks.sheafModuleFiberOfCommRing Φ O) ?_ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) ?_ ?_ A B
  exacts [D.iso, D.naturality_left, D.naturality_right]

/-- **Stacks 0DEN, part (2).** On a ringed site whose underlying site has enough points, a
complex of `O`-modules whose stalk at every point is a K-flat complex of modules over the
stalk of `O` is itself K-flat. -/
theorem kFlat_of_stalks (hJ : J.HasConservativeFamily.{u})
    (D : ∀ Φ : J.Point.{u}, StalkTensorData O Φ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : ∀ Φ : J.Point.{u}, CochainComplex.KFlat.{u, u} (stalkComplex O Φ K)) :
    Stacks.SheafOfModules.IsKFlat O K := by
  have : HasSheafify J AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  obtain ⟨P, hP⟩ := (GrothendieckTopology.hasConservativeFamily_iff_exists J).mp hJ
  intro F hF
  rw [tensorComplex_obj_obj]
  refine (Stacks.acyclic_iff_forall_acyclic_sheafModuleFiberOfCommRing O hP _).mpr fun Φ => ?_
  exact HomologicalComplex.Acyclic.of_iso (totalStalkIso O Φ.obj (D Φ.obj) F K).symm
    (hK Φ.obj (stalkComplex O Φ.obj F) (Stacks.acyclic_map_sheafModuleFiberOfCommRing O Φ.obj hF))

end Tensor

end Stacks.Sheaves.KFlatStalkCriterion

end
