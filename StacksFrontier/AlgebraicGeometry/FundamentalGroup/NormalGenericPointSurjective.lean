module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Surjectivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic point surjects onto the fundamental group of a normal integral scheme

Let `X` be a normal integral scheme with function field `K = κ(η)` at its generic point `η`, and
let `Ω` be an algebraically closed algebraic extension of `K` containing a separable closure `L`
of `K`. The canonical continuous homomorphism

```
Gal(L / K) = π₁(Spec K, η̄) → π₁(X, η̄)
```

of `AlgebraicGeometry.galoisToFundamentalGroup` is surjective.

## Main results

* `AlgebraicGeometry.surjective_galoisToFundamentalGroup` — the surjectivity itself.

## Implementation notes

The Galois-group side of the homomorphism is the identification
`AlgebraicGeometry.galoisEquivEtaleFundamentalGroup` of the absolute Galois group with the étale
fundamental group of `Spec K`, which is bijective, so everything reduces to surjectivity of
`AlgebraicGeometry.etaleFundamentalGroupMap` along `X.fromSpecResidueField (genericPoint X)`.
That is the criterion of Stacks 0BN6, `CategoryTheory.surjective_inducedHom_tfae`,
applied to base change of finite étale covers along the generic point; the transport between the
abstract automorphism groups of that criterion and the étale fundamental groups is
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom`.

The condition of Stacks 0BN6 verified here is the fourth: a categorically connected finite étale
cover `V` of `X` which has a `K`-point over the generic point has a section over `X`. Such a
cover is integral by Stacks 0BQL (`AlgebraicGeometry.isIntegral_of_finite_etale_connected`); the
`K`-point lands on its generic point because the cover is quasi-finite over `X`, and comparing
residue fields there shows that the covering morphism is birational. A finite — hence integral —
birational morphism onto a normal integral scheme is an isomorphism by Stacks 0AB1
(`AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal`), and the section is its
inverse.

Translating `CategoryTheory.PreGaloisCategory.IsConnected` for finite étale covers into
connectedness of the underlying space is done by hand below: a clopen subset of the cover is
again a finite étale cover of `X`, with a monomorphism to the given one which categorical
connectedness forces to be an isomorphism.

## References

* [Stacks Project, Tag 0BQM](https://stacks.math.columbia.edu/tag/0BQM)
* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
* [Stacks Project, Tag 0BQL](https://stacks.math.columbia.edu/tag/0BQL)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Categorically connected finite étale covers have connected spaces -/

/-- A point of a locally quasi-finite scheme over an irreducible base which lies over the generic
point of the base is the generic point of the source. -/
private theorem eq_genericPoint_of_map_eq_genericPoint
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : Y ⟶ X) [LocallyQuasiFinite f] (y : Y) (hy : f y = genericPoint X) :
    y = genericPoint Y := by
  have hspec : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hfgen : f (genericPoint Y) = genericPoint X :=
    ((hspec.map f.continuous).trans (by rw [hy])).antisymm
      ((genericPoint_spec X).specializes (Set.mem_univ _)) |>.eq
  have : DiscreteTopology (f ⁻¹' {genericPoint X}) :=
    (f.isDiscrete_preimage_singleton _).to_subtype
  have heq : (⟨genericPoint Y, hfgen⟩ : f ⁻¹' {genericPoint X}) = ⟨y, hy⟩ :=
    specializes_iff_eq.mp ((subtype_specializes_iff _ _).mpr hspec)
  exact (congrArg Subtype.val heq).symm

/-- **A connected finite étale cover of a normal integral scheme with a rational point over the
generic point is trivial.** The point lands on the generic point of the cover, where the induced
map of residue fields is therefore an isomorphism; so the cover is birational over the base, and
being finite over a normal integral scheme it is an isomorphism. -/
@[ega "II 6.1.15" "special case"]
private theorem isIso_of_finite_etale_section_genericPoint {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormal X] (g : Y ⟶ X) [IsFinite g] [Etale g] [ConnectedSpace Y]
    (σ : Spec (X.residueField (genericPoint X)) ⟶ Y)
    (hσ : σ ≫ g = X.fromSpecResidueField (genericPoint X)) :
    IsIso g := by
  have : IsIntegral Y := isIntegral_of_finite_etale_connected g
  obtain ⟨pt⟩ : Nonempty ↥(Spec (X.residueField (genericPoint X))) := inferInstance
  have hpt : g (σ pt) = genericPoint X := by
    have h := congrArg (fun k : Spec (X.residueField (genericPoint X)) ⟶ X ↦ k.base pt) hσ
    exact h.trans (Scheme.fromSpecResidueField_apply (genericPoint X) pt)
  have hgen : σ pt = genericPoint Y :=
    eq_genericPoint_of_map_eq_genericPoint g (σ pt) hpt
  have hpre : IsPreimmersion (σ ≫ g) := by
    rw [hσ]
    infer_instance
  have hcompiso : IsIso (g.residueFieldMap (σ pt) ≫ σ.residueFieldMap pt) := by
    rw [← Scheme.residueFieldMap_comp]
    exact isIso_residueFieldMap_of_isPreimmersion (σ ≫ g) pt
  have hsnd : IsIso (σ.residueFieldMap pt) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨(σ.residueFieldMap pt).hom.injective, ?_⟩
    have hb := (ConcreteCategory.bijective_of_isIso
      (g.residueFieldMap (σ pt) ≫ σ.residueFieldMap pt)).2
    exact Function.Surjective.of_comp (g := (g.residueFieldMap (σ pt)).hom) hb
  have hrf : IsIso (g.residueFieldMap (σ pt)) :=
    IsIso.of_isIso_comp_right _ (σ.residueFieldMap pt)
  have hresX : IsIso (X.residue (g (σ pt))) := by
    rw [hpt]; exact AlgebraicGeometry.isIso_residue_genericPoint X
  have hresY : IsIso (Y.residue (σ pt)) := by
    rw [hgen]; exact AlgebraicGeometry.isIso_residue_genericPoint Y
  have hstalkcomp : IsIso (g.stalkMap (σ pt) ≫ Y.residue (σ pt)) := by
    rw [← Scheme.residue_residueFieldMap g (σ pt)]
    infer_instance
  have hstalk : IsIso (g.stalkMap (σ pt)) :=
    IsIso.of_isIso_comp_right _ (Y.residue (σ pt))
  have hptgen : g (genericPoint Y) = genericPoint X := hgen ▸ hpt
  have hbij : Set.BijOn g (genericPoints Y) (genericPoints X) := by
    rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    simp [hptgen]
  have hbir : IsBirational g :=
    isBirational_of_bijOn_of_isIso_stalkMap g hbij fun w hw ↦ by
      obtain rfl : w = σ pt := by
        rw [hgen]
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hw
      exact hstalk
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal g hbir

/-! ### Surjectivity -/

/-- **Base change along the generic point induces a surjection of étale fundamental groups.**
This is the criterion of Stacks 0BN6, whose fourth condition is
`AlgebraicGeometry.isIso_of_finite_etale_section_genericPoint`. -/
@[sga "1 V 8.2" "more general"]
private theorem surjective_etaleFundamentalGroupMap_fromSpecResidueField
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (x : GeometricPoint (Spec (X.residueField (genericPoint X)))) :
    Function.Surjective
      (etaleFundamentalGroupMap (X.fromSpecResidueField (genericPoint X)) x) := by
  let S := Spec (X.residueField (genericPoint X))
  let j : S ⟶ X := X.fromSpecResidueField (genericPoint X)
  let H := finiteEtaleBaseChange j
  let F := finiteEtaleFiberFintypeFunctor X (x.map j)
  let F' := finiteEtaleFiberFintypeFunctor S x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso j x
  let d := CategoryTheory.galoisFunctorDataOfFiberIso F F' H t
  let _gF : CategoryTheory.IsGaloisCategory
      (CategoryTheory.setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X (x.map j)
  let _gF' : CategoryTheory.IsGaloisCategory
      (CategoryTheory.setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor S x
  let star := finiteEtaleOverTerminal X
  let star' := finiteEtaleOverTerminal S
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange j x
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have hdsurj : Function.Surjective d.hom := by
    apply ((CategoryTheory.surjective_inducedHom_tfae
      F F' H hH t d star star' hs hs' hHs).out 4 1).mp
    rintro V hV ⟨p⟩
    let VX : V.left ⟶ X := V.hom
    have hVXfin : IsFinite VX := V.prop.1
    have hVXet : Etale VX := V.prop.2
    let v : S ⟶ V.left := p.left ≫ pullback.fst VX j
    have hv : v ≫ VX = j := by
      have hw : p.left ≫ pullback.snd VX j = 𝟙 _ := p.w
      have h1 : pullback.fst VX j ≫ VX = pullback.snd VX j ≫ j := pullback.condition
      have h3 : (p.left ≫ pullback.fst VX j) ≫ VX
          = (p.left ≫ pullback.snd VX j) ≫ j :=
        (Category.assoc _ _ _).trans
          ((congrArg (p.left ≫ ·) h1).trans (Category.assoc _ _ _).symm)
      exact h3.trans ((congrArg (· ≫ j) hw).trans (Category.id_comp j))
    have hconn : ConnectedSpace V.left := connectedSpace_left_of_isConnected V hV
    obtain ⟨w, -, hw⟩ := (isIso_of_finite_etale_section_genericPoint VX v hv).out
    exact ⟨MorphismProperty.Over.homMk w hw⟩
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup X (x.map j)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup S x σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom j x d σ, hσ]
  exact (autMulEquivEtaleFundamentalGroup X (x.map j)).apply_symm_apply ρ

/-- **Stacks 0BQM, surjectivity.** For a normal integral scheme `X` with function field
`K = κ(η)` at its generic point `η`, a separable closure `L` of `K` and an algebraically closed
algebraic extension `Ω` of `K` containing `L`, the canonical continuous homomorphism

```
Gal(L / K) → π₁(X, η̄)
```

is surjective. Equivalently, every connected finite étale cover of `X` stays connected over the
function field. -/
@[stacks 0BQM "surjectivity of the generic-point map", sga "1 V 8.2" "surjectivity"]
theorem surjective_galoisToFundamentalGroup
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (X.residueField (genericPoint X)) L]
    [IsSepClosure (X.residueField (genericPoint X)) L]
    [Algebra L Ω] [Algebra (X.residueField (genericPoint X)) Ω]
    [IsScalarTower (X.residueField (genericPoint X)) L Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic (X.residueField (genericPoint X)) Ω] :
    Function.Surjective (galoisToFundamentalGroup X L Ω) := by
  intro ρ
  obtain ⟨τ, rfl⟩ := surjective_etaleFundamentalGroupMap_fromSpecResidueField X
    (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω) ρ
  obtain ⟨g, rfl⟩ :=
    (galoisEquivEtaleFundamentalGroup (X.residueField (genericPoint X)) L Ω).surjective τ
  exact ⟨g, rfl⟩

end AlgebraicGeometry

end
