module

public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentComparison
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality

/-!
# Compatibility of the affine comparison map with restriction to smaller opens

Let `f : X ⟶ Y` be a morphism of schemes, let `U' ≤ U` be opens of `X` and `V' ≤ V` opens of
`Y` with `f(U) ⊂ V` and `f(U') ⊂ V'`. Writing `A = 𝒪_Y(V)`, `B = 𝒪_X(U)`, `A' = 𝒪_Y(V')` and
`B' = 𝒪_X(U')`, the restriction maps form a commutative square of ring maps `A → A'`, `B → B'`
and therefore a canonical map `L_{B/A} ⟶ L_{B'/A'}` of cotangent complexes. This file proves
that the canonical map `L_{B/A} ⟶ L_{X/Y}(U)` of
`AlgebraicGeometry.Scheme.Hom.cotangentSectionsComparison` commutes with these two
restrictions.

The map being compared is a composite of two steps, and so is the proof:

* the functoriality of the cotangent complex of a ring map in the square
  `𝒪_Y(V) → (f⁻¹𝒪_Y)(U)`, `𝒪_X(U) = 𝒪_X(U)` of
  `AlgebraicGeometry.Scheme.Hom.affineAlgebraSquare`. This step is compatible with restriction
  because the canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` is
  (`AlgebraicGeometry.Scheme.Hom.inverseImageSections_restriction`, which identifies the two
  composite squares in `AlgebraicGeometry.Scheme.Hom.affineAlgebraSquare_comp`) and because the
  functoriality of the cotangent complex is itself functorial in the square
  (`CommAlgCat.squareCotangentComplexMap_comp_apply`);
* the canonical map of Remark 08SX on sections over `U`, whose compatibility with the
  restriction maps of the site is
  `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_restriction`, the clause (2) of
  Remark 08SX proved in
  `StacksFrontier/Cotangent/SheavesOfRings/SectionsComparisonNaturality.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.affineRestrictionSquare` is the commutative square of ring maps
  given by the two restriction maps `𝒪_Y(V) → 𝒪_Y(V')` and `𝒪_X(U) → 𝒪_X(U')`.

## Main results

* `CommAlgCat.squareCotangentComplexMap_comp_apply`,
  `CommAlgCat.squareCotangentComplexMap_comp` and `CommAlgCat.cotangentComplexAbMap_comp`: the
  functoriality of the cotangent complex of a ring map in a commutative square of rings is
  compatible with the horizontal composition of squares, at the level of complexes.
* `AlgebraicGeometry.Scheme.Hom.inverseImageSections_restriction`: the canonical ring map
  `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` is compatible with restriction to `V' ≤ V` and `U' ≤ U`.
* `AlgebraicGeometry.Scheme.Hom.affineAlgebraSquare_comp`: the two ways of composing the
  squares — restrict and then pass to `f⁻¹𝒪_Y`, or pass to `f⁻¹𝒪_Y` and then restrict — give
  the same square of ring maps.
* `AlgebraicGeometry.Scheme.Hom.cotangentSectionsComparison_restriction_degree` and
  `AlgebraicGeometry.Scheme.Hom.cotangentSectionsComparison_restriction`: the canonical map
  `L_{𝒪_X(U)/𝒪_Y(V)} ⟶ L_{X/Y}(U)` commutes with restriction to `U' ≤ U` and `V' ≤ V`.

## Implementation notes

Carried hypotheses: a morphism of schemes `f : X ⟶ Y`, opens `U' ≤ U` of `X` and `V' ≤ V` of
`Y`, and the two containments `U ≤ f⁻¹V` and `U' ≤ f⁻¹V'`. Affineness of none of the four opens
is carried: the comparison map it is about is built for an arbitrary open `U` (see the
implementation notes of
`StacksFrontier/Cotangent/SheavesOfRings/AffineCotangentComparison.lean`), and its compatibility
with restriction does not use affineness either. In particular neither `IsAffineOpen U'` nor
`IsAffineOpen V'` appears. This generalizes the hypotheses of the source statement rather than
weakening its conclusion.

`CommAlgCat.squareCotangentComplexMap_comp` is stated without any comparison isomorphism
between `ModuleCat.restrictScalars (sq'.map.comp sq.map)` and the iterated restriction of
scalars: for `CommAlgCat.AlgebraSquare.comp` the composite square's map *is* the composite ring
map, and `Module.compHom (Module.compHom M g) f` is definitionally `Module.compHom M (g.comp f)`,
so the two targets agree on the nose. The `ModuleCat.restrictScalarsComp'App` comparison does
appear inside the proof, in the auxiliary equality the term extensionality lemma is applied to:
there both sides must have the *same* target syntactically, or the unification of that target
is what the elaboration budget is spent on.

The composition laws are stated with the algebra universe equal to the base-ring universe,
which is the instance the schemes below need (`CommAlgCat.{u}` over `Type u`). With the two
universes independent the statements still typecheck but the elaborator spends its whole budget
on `isDefEq` for the iterated restriction of scalars; nothing in the proof depends on the
universes being equal.

The proof of `AlgebraicGeometry.Scheme.Hom.inverseImageSections_restriction` is written in term
mode. The statement mixes `Y.presheaf` with the sheaf `Y.sheaf` of commutative rings on the
small Zariski site, which are the same presheaf only up to unfolding `TopCat.Sheaf`; `rw` and
`simp` refuse to rewrite through that, while `Eq.trans` and `congrArg` are happy.

## References

* [Stacks Project, Tag 08T3](https://stacks.math.columbia.edu/tag/08T3)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite Simplicial
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace CommAlgCat

/-! ### Functoriality of the cotangent complex in a composite of squares -/

/-- Two commutative squares of ring maps with the same base map and the same map of algebras
are equal: the commutativity condition is a proposition. -/
private theorem algebraSquare_eq_of_fields {A A' : Type u} [CommRing A] [CommRing A']
    {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
    {sq sq' : AlgebraSquare.{u, u, u} A A' B B'}
    (hbase : sq.base = sq'.base) (hmap : sq.map = sq'.map) : sq = sq' := by
  obtain ⟨b, m, hbm⟩ := sq
  obtain ⟨b', m', hbm'⟩ := sq'
  subst hbase
  subst hmap
  rfl

/-- From `e.hom x = y` one gets `x = e.inv y`, for an isomorphism of modules. -/
private theorem eq_inv_apply_of_hom_eq {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) {x : M} {y : N} (h : e.hom x = y) : x = e.inv y :=
  (Iso.hom_inv_id_apply e x).symm.trans (congrArg (fun z => e.inv z) h)

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'} {B'' : CommAlgCat.{u} A''}

/-- **The map of cotangent complexes induced by a composite of squares is the composite of the
induced maps**, elementwise in every cohomological degree. Restriction of scalars does not change
the underlying type, so no comparison between `ModuleCat.restrictScalars (sq'.map.comp sq.map)`
and the iterated restriction of scalars appears in this form of the statement. -/
theorem squareCotangentComplexMap_comp_apply (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') (j : ℤ)
    (x : (cotangentComplex.{u, u} A B).X j) :
    (squareCotangentComplexMap.{u, u, u} (sq.comp sq')).f j x =
      (squareCotangentComplexMap.{u, u, u} sq').f j
        ((squareCotangentComplexMap.{u, u, u} sq).f j x) := by
  by_cases hpos : 0 < j
  · exact ConcreteCategory.congr_hom
      ((cotangentComplex_isZero_pos.{u, u} A B j hpos).eq_of_src
        ((squareCotangentComplexMap.{u, u, u} (sq.comp sq')).f j)
        ((squareCotangentComplexMap.{u, u, u} sq).f j ≫
          (ModuleCat.restrictScalars sq.map).map
            ((squareCotangentComplexMap.{u, u, u} sq').f j))) x
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    have heq : (cotangentComplex_degreeIso.{u, u} A B n).inv ≫
          (squareCotangentComplexMap.{u, u, u} (sq.comp sq')).f (-(n : ℤ)) =
        (cotangentComplex_degreeIso.{u, u} A B n).inv ≫
          (squareCotangentComplexMap.{u, u, u} sq).f (-(n : ℤ)) ≫
            (ModuleCat.restrictScalars sq.map).map
              ((squareCotangentComplexMap.{u, u, u} sq').f (-(n : ℤ))) ≫
              (ModuleCat.restrictScalarsComp'App sq.map sq'.map (sq.comp sq').map rfl
                ((cotangentComplex.{u, u} A'' B'').X (-(n : ℤ)))).inv := by
      refine cotangentTerm_hom_ext.{u, u} A B (op ⦋n⦌) _ _ fun p => ?_
      have hp := squareCotangentComplexMap_differential.{u, u, u} (sq.comp sq') n p
      have hg := squareCotangentComplexMap_differential.{u, u, u} sq n p
      have hh := squareCotangentComplexMap_differential.{u, u, u} sq' n
        (standardResolutionSquareMap.{u, u, u} sq (op ⦋n⦌) p)
      have hres : standardResolutionSquareMap.{u, u, u} (sq.comp sq') (op ⦋n⦌) p =
          standardResolutionSquareMap.{u, u, u} sq' (op ⦋n⦌)
            (standardResolutionSquareMap.{u, u, u} sq (op ⦋n⦌) p) :=
        RingHom.congr_fun (standardResolutionSquareMap_comp.{u, u} sq sq' (op ⦋n⦌)) p
      rw [hres] at hp
      exact (eq_inv_apply_of_hom_eq _ hp).trans
        ((congrArg (fun z => (squareCotangentComplexMap.{u, u, u} sq').f (-(n : ℤ)) z)
          (eq_inv_apply_of_hom_eq _ hg)).trans
            (eq_inv_apply_of_hom_eq (cotangentComplex_degreeIso.{u, u} A'' B'' n) hh)).symm
    exact ConcreteCategory.congr_hom
      ((cancel_epi (cotangentComplex_degreeIso.{u, u} A B n).inv).mp heq) x

/-- **The map of cotangent complexes induced by a composite of squares is the composite of the
induced maps**, as an equality of maps of modules in every cohomological degree. The target of
the map induced by the composite square is read over `B` along `sq'.map.comp sq.map`, which is
the restriction of scalars along `sq.map` of the restriction of scalars along `sq'.map`. -/
theorem squareCotangentComplexMap_comp (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') (j : ℤ) :
    (squareCotangentComplexMap.{u, u, u} (sq.comp sq')).f j =
      (squareCotangentComplexMap.{u, u, u} sq).f j ≫
        (ModuleCat.restrictScalars sq.map).map
          ((squareCotangentComplexMap.{u, u, u} sq').f j) :=
  ConcreteCategory.hom_ext _ _ (squareCotangentComplexMap_comp_apply.{u} sq sq' j)

/-- The elementwise composition law, with the composite square given by an equation. This is the
form in which the law is applied to a square that is a composite in two different ways. -/
theorem squareCotangentComplexMap_apply_of_eq_comp (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'')
    {sqc : AlgebraSquare.{u, u, u} A A'' B B''} (h : sqc = sq.comp sq') (j : ℤ)
    (x : (cotangentComplex.{u, u} A B).X j) :
    (squareCotangentComplexMap.{u, u, u} sqc).f j x =
      (squareCotangentComplexMap.{u, u, u} sq').f j
        ((squareCotangentComplexMap.{u, u, u} sq).f j x) := by
  subst h
  exact squareCotangentComplexMap_comp_apply.{u} sq sq' j x

/-- **The map of cotangent complexes induced by a composite of squares is the composite of the
induced maps**, as an equality of maps of complexes of abelian groups. -/
theorem cotangentComplexAbMap_comp (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') :
    cotangentComplexAbMap.{u, u, u} (sq.comp sq') =
      cotangentComplexAbMap.{u, u, u} sq ≫ cotangentComplexAbMap.{u, u, u} sq' := by
  ext j x
  exact squareCotangentComplexMap_comp_apply.{u} sq sq' j x

end CommAlgCat

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` and restriction -/

/-- **The canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` is compatible with restriction.** Restricting
from `V` to `V' ≤ V` on the source and from `U` to `U' ≤ U` on the target gives the canonical
map attached to the containment `U' ≤ f⁻¹V'`. -/
theorem inverseImageSections_restriction {U U' : X.Opens} {V V' : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') (hU' : U' ≤ U) (hV' : V' ≤ V) :
    inverseImageSections f e ≫ (zariskiInverseImageStructureSheaf f).obj.map (homOfLE hU').op =
      Y.presheaf.map (homOfLE hV').op ≫ inverseImageSections f e' :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (inverseImageUnit f).hom.app (op V) ≫ z)
        (((zariskiInverseImageStructureSheaf f).obj.map_comp
          (homOfLE e).op (homOfLE hU').op).symm)).trans
      ((congrArg (fun z => (inverseImageUnit f).hom.app (op V) ≫ z)
          ((zariskiInverseImageStructureSheaf f).obj.map_comp
            ((Opens.map f.base).map (homOfLE hV')).op (homOfLE e').op)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (zariskiInverseImageStructureSheaf f).obj.map (homOfLE e').op)
              ((inverseImageUnit f).hom.naturality (homOfLE hV').op).symm).trans
            (Category.assoc _ _ _)))))

/-! ### The square of restriction maps -/

section Square

variable {U U' : X.Opens} {V V' : Y.Opens}

/-- The commutative square of ring maps given by restricting to smaller opens `U' ≤ U` of `X`
and `V' ≤ V` of `Y`: the restriction maps of `𝒪_Y` and of `𝒪_X`, over the two algebra
structures given by `f`. -/
def affineRestrictionSquare (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hU' : U' ≤ U) (hV' : V' ≤ V) :
    CommAlgCat.AlgebraSquare.{u, u, u} Γ(Y, V) Γ(Y, V')
        (affineAlgebra f e) (affineAlgebra f e') where
  base := (Y.presheaf.map (homOfLE hV').op).hom
  map := (X.presheaf.map (homOfLE hU').op).hom
  map_algebraMap a :=
    congrArg (fun k : Γ(Y, V) ⟶ Γ(X, U') => k.hom a)
      (show f.appLE V U e ≫ X.presheaf.map (homOfLE hU').op =
          Y.presheaf.map (homOfLE hV').op ≫ f.appLE V' U' e' by simp)

/-- The restriction square of the small Zariski site attached to `U' ≤ U`, for the homomorphism
`f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings. -/
abbrev zariskiSectionsRestrictionSquare (hU' : U' ≤ U) :
    CommAlgCat.AlgebraSquare.{u, u, u}
      ((zariskiInverseImageStructureSheaf f).obj.obj (op U))
      ((zariskiInverseImageStructureSheaf f).obj.obj (op U'))
      (inverseImageSectionsAlgebra f U) (inverseImageSectionsAlgebra f U') :=
  CategoryTheory.Sheaf.sectionsRestrictionSquare (Opens.grothendieckTopology ↥X)
    (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (homOfLE hU').op

/-- **The two ways of composing the squares agree.** Passing from `𝒪_Y(V)` to `(f⁻¹𝒪_Y)(U)` and
then restricting to `U'` is the same square of ring maps as restricting to `V'` and `U'` and
then passing from `𝒪_Y(V')` to `(f⁻¹𝒪_Y)(U')`. -/
theorem affineAlgebraSquare_comp (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hU' : U' ≤ U) (hV' : V' ≤ V) :
    (affineAlgebraSquare f e).comp (zariskiSectionsRestrictionSquare f hU') =
      (affineRestrictionSquare f e e' hU' hV').comp (affineAlgebraSquare f e') :=
  CommAlgCat.algebraSquare_eq_of_fields
    (congrArg CommRingCat.Hom.hom (inverseImageSections_restriction f e e' hU' hV')) rfl

end Square

/-! ### The comparison on sections and restriction -/

section Comparison

variable {U U' : X.Opens} {V V' : Y.Opens}

/-- **Stacks 08T3, the compatibility with restriction.** The canonical map
`L_{𝒪_X(U)/𝒪_Y(V)} ⟶ L_{X/Y}(U)` commutes with restricting to smaller opens `U' ≤ U` of `X`
and `V' ≤ V` of `Y`: the source's restriction map is the functoriality of the cotangent complex
of a ring map in the square `AlgebraicGeometry.Scheme.Hom.affineRestrictionSquare` of
restriction maps, and the target's is the restriction map of the sheaf of modules `L_{X/Y}`. -/
theorem cotangentSectionsComparison_restriction (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hU' : U' ≤ U) (hV' : V' ≤ V) (j : ℤ)
    (x : (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X j) :
    (f.cotangentComplex.X j).val.map (homOfLE hU').op
        ((cotangentSectionsComparison f e).f j x) =
      (cotangentSectionsComparison f e').f j
        ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
          (affineRestrictionSquare f e e' hU' hV')).f j x) := by
  have h08SX := CategoryTheory.Sheaf.sectionsCotangentComplexComparison_restriction.{u, u, u}
    (Opens.grothendieckTopology ↥X)
    (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (homOfLE hU').op j
    ((CommAlgCat.squareCotangentComplexMap.{u, u, u} (affineAlgebraSquare f e)).f j x)
  have hleft := CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp.{u}
    (affineAlgebraSquare f e) (zariskiSectionsRestrictionSquare f hU') rfl j x
  have hright := CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp.{u}
    (affineRestrictionSquare f e e' hU' hV') (affineAlgebraSquare f e')
    (affineAlgebraSquare_comp f e e' hU' hV') j x
  refine h08SX.trans (congrArg (fun z =>
    (CategoryTheory.Sheaf.sectionsCotangentComplexComparison.{u, u, u}
      (Opens.grothendieckTopology ↥X)
      (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (op U')).f j z) ?_)
  exact hleft.symm.trans hright

/-- **Stacks 08T3, the compatibility with restriction**, as an equality of maps of
`𝒪_X(U)`-modules in a single cohomological degree. The target of the right-hand composite is
read over `𝒪_X(U)` along the restriction map `𝒪_X(U) → 𝒪_X(U')`. -/
theorem cotangentSectionsComparison_restriction_degree (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V')
    (hU' : U' ≤ U) (hV' : V' ≤ V) (j : ℤ) :
    (cotangentSectionsComparison f e).f j ≫
        (f.cotangentComplex.X j).val.map (homOfLE hU').op =
      (CommAlgCat.squareCotangentComplexMap.{u, u, u}
          (affineRestrictionSquare f e e' hU' hV')).f j ≫
        (ModuleCat.restrictScalars (affineRestrictionSquare f e e' hU' hV').map).map
          ((cotangentSectionsComparison f e').f j) :=
  ConcreteCategory.hom_ext _ _
    (cotangentSectionsComparison_restriction f e e' hU' hV' j)

end Comparison

end AlgebraicGeometry.Scheme.Hom

end
