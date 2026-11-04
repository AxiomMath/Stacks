module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.DirectedColimit

/-!
# The sectionwise cotangent complex of a homomorphism of sheaves of rings

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. Over every object `U`
of the site it restricts to a ring map `A(U) → B(U)`, whose cotangent complex
`L_{B(U)/A(U)}` is the cotangent complex of a ring map. Restricting along a morphism `U ⟶ V`
moves both rings, so the comparison maps are the functoriality of the cotangent complex in a
*square* of ring maps; this file checks that they make `U ↦ L_{B(U)/A(U)}` a presheaf of
complexes of abelian groups, and names its cohomology presheaves
`U ↦ H^i(L_{B(U)/A(U)})`.

## Main definitions

* `CategoryTheory.Sheaf.sectionsAlgebra` presents the sections `B(U)` as an `A(U)`-algebra.
* `CategoryTheory.Sheaf.sectionsRestrictionSquare` is the commutative square of ring maps given
  by restricting `A ⟶ B` along `U ⟶ V`.
* `CategoryTheory.Sheaf.sectionwiseCotangentComplex` is the presheaf of complexes of abelian
  groups `U ↦ L_{B(U)/A(U)}`.
* `CategoryTheory.Sheaf.sectionwiseCotangentCohomology` is its `i`-th cohomology presheaf
  `U ↦ H^i(L_{B(U)/A(U)})`.

## Main results

* `CategoryTheory.Sheaf.cotangentComplexAbMap_sectionsRestrictionSquare_id` and
  `CategoryTheory.Sheaf.cotangentComplexAbMap_sectionsRestrictionSquare_comp`: the comparison
  maps of the restriction squares are unital and multiplicative, which is what makes the
  presheaves above well defined.
* `CategoryTheory.Sheaf.sectionwiseCotangentCohomology_obj`: the cohomology presheaf has
  sections `H^i(L_{B(U)/A(U)})` over `U`.

## Implementation notes

The presheaf is formed at the level of abelian groups. In simplicial degree `n` the term of
`L_{B(U)/A(U)}` is a module over the varying ring `B(U)`, and the comparison map of a
restriction square is `B(U)`-linear for the source ring only, so there is no one ring over
which the whole system is linear; abelian groups is also the level at which Stacks 08SW takes
the sheafification. Nothing is lost: the forgetful functor is faithful and exact, so the
cohomology of the complex of abelian groups underlying `L_{B(U)/A(U)}` is `H^i(L_{B(U)/A(U)})`.
The complex of abelian groups and the map induced by a square are
`CommAlgCat.cotangentComplexAb` and `CommAlgCat.cotangentComplexAbMap`, which the directed
colimit development already provides.

Both functor laws are proved degreewise. Above degree zero the terms vanish
(`CommAlgCat.cotangentComplex_isZero_pos`), and in degree `-n` two maps out of the term agree as
soon as they agree on the pure differentials `1 ⊗ d p`
(`CommAlgCat.cotangentTerm_hom_ext`), where the defining property
`CommAlgCat.SquareFunctorialityData.complexMap_differential` of the comparison map applies. On
the two sides of each law the target is read over a different ring — along the composite map for
one and along the two maps in turn for the other — so the comparison of the two restrictions of
scalars, `ModuleCat.restrictScalarsId'App` and `ModuleCat.restrictScalarsComp'App`, appears in
the degreewise statements; it disappears on underlying abelian groups, which is where the laws
are stated.

### Where Tag 08SW is stated

Tag 08SW says that `H^i(L_{B/A})` is the sheaf associated to the presheaf
`U ↦ H^i(L_{B(U)/A(U)})`. This file builds that presheaf; the identification itself is
`CategoryTheory.Sheaf.cohomologySheafification` in
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplexIso.lean`, which carries the
tag. The route there refines the presheaf of this file to a presheaf of `B`-modules
(`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentModules.lean`), identifies the
sheafification of each of its terms with the corresponding term of `L_{B/A}`
(`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentSheafification.lean`), assembles
those into an isomorphism of complexes, and moves `H^i` across the exact functors in play.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w s t

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The ring map `A(U) → B(U)` on sections over `U`. -/
noncomputable abbrev sectionsMap (U : Cᵒᵖ) : A.obj.obj U →+* B.obj.obj U :=
  (f.hom.app U).hom

/-- The sections `B(U)`, viewed as an algebra over the sections `A(U)`. -/
noncomputable abbrev sectionsAlgebra (U : Cᵒᵖ) : CommAlgCat.{max u v w} (A.obj.obj U) :=
  letI : Algebra (A.obj.obj U) (B.obj.obj U) := (sectionsMap J f U).toAlgebra
  CommAlgCat.of (A.obj.obj U) (B.obj.obj U)

/-- The cotangent complex `L_{B(U)/A(U)}` of the ring map on sections over `U`, as a complex of
abelian groups. -/
noncomputable abbrev sectionsCotangentComplexAb (U : Cᵒᵖ) :
    CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  CommAlgCat.cotangentComplexAb.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U)

/-- Restricting `A ⟶ B` along `U ⟶ V` gives a commutative square of ring maps
`A(U) → A(V)`, `B(U) → B(V)` over the two algebra structures. -/
noncomputable def sectionsRestrictionSquare {U V : Cᵒᵖ} (g : U ⟶ V) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w}
      (A.obj.obj U) (A.obj.obj V) (sectionsAlgebra J f U) (sectionsAlgebra J f V) where
  base := (A.obj.map g).hom
  map := (B.obj.map g).hom
  map_algebraMap a := by
    change (B.obj.map g).hom (sectionsMap J f U a) = sectionsMap J f V ((A.obj.map g).hom a)
    exact congrArg (fun k : A.obj.obj U ⟶ B.obj.obj V => k.hom a) (f.hom.naturality g).symm

/-- The restriction square of an identity is the identity square. -/
theorem sectionsRestrictionSquare_id (U : Cᵒᵖ) :
    sectionsRestrictionSquare J f (𝟙 U) =
      CommAlgCat.AlgebraSquare.id.{max u v w, max u v w} _ (sectionsAlgebra J f U) := by
  have hbase := congrArg CommRingCat.Hom.hom (A.obj.map_id U)
  have hmap := congrArg CommRingCat.Hom.hom (B.obj.map_id U)
  unfold sectionsRestrictionSquare CommAlgCat.AlgebraSquare.id
  simp only [hbase, hmap]
  rfl

/-- The restriction square of a composite is the composite of the restriction squares. -/
theorem sectionsRestrictionSquare_comp {U V W : Cᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) :
    sectionsRestrictionSquare J f (g ≫ h) =
      (sectionsRestrictionSquare J f g).comp (sectionsRestrictionSquare J f h) := by
  have hbase := congrArg CommRingCat.Hom.hom (A.obj.map_comp g h)
  have hmap := congrArg CommRingCat.Hom.hom (B.obj.map_comp g h)
  unfold sectionsRestrictionSquare CommAlgCat.AlgebraSquare.comp
  simp only [hbase, hmap]
  rfl

/-- From `e.hom x = y` one gets `x = e.inv y`, for an isomorphism of modules. -/
private theorem eq_inv_apply_of_hom_apply_eq {R : Type t} [CommRing R]
    {M N : ModuleCat.{s} R} (e : M ≅ N) {x : M} {y : N} (hxy : e.hom x = y) :
    x = e.inv y := by
  rw [← hxy, ModuleCat.inv_hom_apply]

/-- From `e.hom x = y` one gets `x = e.inv y`, for an isomorphism of modules; the public form of
the private lemma above, for the files that build on this one. -/
alias eq_inv_apply_of_hom_apply_eq' := eq_inv_apply_of_hom_apply_eq

/-- Two maps out of `L_{B(U)/A(U)}` agree if they agree in every degree `-n` with `n : ℕ`, since
the terms vanish in positive degrees. -/
private theorem cotangentComplexAb_hom_ext (U : Cᵒᵖ)
    {L : CochainComplex AddCommGrpCat.{max u v w} ℤ}
    (φ ψ : sectionsCotangentComplexAb J f U ⟶ L)
    (h : ∀ (n : ℕ) x, φ.f (-(n : ℤ)) x = ψ.f (-(n : ℤ)) x) : φ = ψ := by
  ext degree x
  by_cases hdegree : 0 < degree
  · have hzero := CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U) degree hdegree
    have hx : x = 0 := (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _
    subst hx
    simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, degree = -(n : ℤ) := ⟨(-degree).toNat, by omega⟩
    exact h n x

/-- **The comparison map of the identity restriction square is the identity.** -/
theorem cotangentComplexAbMap_sectionsRestrictionSquare_id (U : Cᵒᵖ) :
    CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f (𝟙 U)) = 𝟙 _ := by
  refine cotangentComplexAb_hom_ext J f U _ _ fun n x => ?_
  set e := CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n with he
  set mapId := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f (𝟙 U))).complexMap.f (-(n : ℤ)) with hmapId
  have heq : e.inv ≫ mapId =
      e.inv ≫ (ModuleCat.restrictScalarsId'App
        (sectionsRestrictionSquare J f (𝟙 U)).map
        (congrArg CommAlgCat.AlgebraSquare.map (sectionsRestrictionSquare_id J f U))
        ((CommAlgCat.cotangentComplex.{max u v w, max u v w}
          (A.obj.obj U) (sectionsAlgebra J f U)).X (-(n : ℤ)))).inv := by
    refine CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} _ _ _ _ _ fun p => ?_
    have hp := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f (𝟙 U))).complexMap_differential n p
    rw [sectionsRestrictionSquare_id,
      CommAlgCat.squareFunctoriality_resolution_id.{max u v w, max u v w}] at hp
    rw [← sectionsRestrictionSquare_id J f U] at hp
    have hp' := eq_inv_apply_of_hom_apply_eq.{max u v w, max u v w} e hp
    change mapId (e.inv (CommAlgCat.cotangentTermDifferential _ _ _ p)) =
      e.inv (CommAlgCat.cotangentTermDifferential _ _ _ p)
    exact hp'
  have hx := ConcreteCategory.congr_hom ((cancel_epi e.inv).mp heq) x
  change mapId x = x
  exact hx

/-- **The comparison maps of restriction squares compose.** -/
theorem cotangentComplexAbMap_sectionsRestrictionSquare_comp {U V W : Cᵒᵖ}
    (g : U ⟶ V) (h : V ⟶ W) :
    CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f (g ≫ h)) =
      CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) ≫
        CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f h) := by
  refine cotangentComplexAb_hom_ext J f U _ _ fun n x => ?_
  set eU := CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n with heU
  set eV := CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj V) (sectionsAlgebra J f V) n with heV
  set eW := CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj W) (sectionsAlgebra J f W) n with heW
  set mapG := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g)).complexMap.f (-(n : ℤ)) with hmapG
  set mapH := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f h)).complexMap.f (-(n : ℤ)) with hmapH
  set mapGH := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f (g ≫ h))).complexMap.f (-(n : ℤ)) with hmapGH
  have heq : eU.inv ≫ mapGH =
      eU.inv ≫ mapG ≫
        (ModuleCat.restrictScalars (sectionsRestrictionSquare J f g).map).map mapH ≫
        (ModuleCat.restrictScalarsComp'App (sectionsRestrictionSquare J f g).map
          (sectionsRestrictionSquare J f h).map
          (sectionsRestrictionSquare J f (g ≫ h)).map
          (congrArg CommAlgCat.AlgebraSquare.map
            (sectionsRestrictionSquare_comp J f g h))
          ((CommAlgCat.cotangentComplex.{max u v w, max u v w}
            (A.obj.obj W) (sectionsAlgebra J f W)).X (-(n : ℤ)))).inv := by
    refine CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} _ _ _ _ _ fun p => ?_
    have hp := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f (g ≫ h))).complexMap_differential n p
    have hg := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).complexMap_differential n p
    have hh := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f h)).complexMap_differential n
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution (op ⦋n⦌) p)
    rw [sectionsRestrictionSquare_comp,
      CommAlgCat.squareFunctoriality_resolution_comp.{max u v w, max u v w}] at hp
    rw [← sectionsRestrictionSquare_comp J f g h] at hp
    have hp' := eq_inv_apply_of_hom_apply_eq.{max u v w, max u v w} eW hp
    have hg' := eq_inv_apply_of_hom_apply_eq.{max u v w, max u v w} eV hg
    have hh' := eq_inv_apply_of_hom_apply_eq.{max u v w, max u v w} eW hh
    rw [← hg'] at hh'
    change mapGH (eU.inv (CommAlgCat.cotangentTermDifferential _ _ _ p)) =
      mapH (mapG (eU.inv (CommAlgCat.cotangentTermDifferential _ _ _ p)))
    exact hp'.trans hh'.symm
  have hx := ConcreteCategory.congr_hom ((cancel_epi eU.inv).mp heq) x
  change mapGH x = mapH (mapG x)
  exact hx

/-- **The presheaf of sectionwise cotangent complexes** `U ↦ L_{B(U)/A(U)}`, with the comparison
maps of the restriction squares as restriction maps. -/
noncomputable def sectionwiseCotangentComplex :
    Cᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max u v w} ℤ where
  obj U := sectionsCotangentComplexAb J f U
  map g := CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g)
  map_id U := cotangentComplexAbMap_sectionsRestrictionSquare_id J f U
  map_comp g h := cotangentComplexAbMap_sectionsRestrictionSquare_comp J f g h

/-- The value of the sectionwise cotangent complex at `U` is `L_{B(U)/A(U)}`. -/
@[simp]
theorem sectionwiseCotangentComplex_obj (U : Cᵒᵖ) :
    (sectionwiseCotangentComplex J f).obj U = sectionsCotangentComplexAb J f U :=
  rfl

/-- The restriction map of the sectionwise cotangent complex along `g : U ⟶ V` is the comparison
map of the restriction square of `g`. -/
@[simp]
theorem sectionwiseCotangentComplex_map {U V : Cᵒᵖ} (g : U ⟶ V) :
    (sectionwiseCotangentComplex J f).map g =
      CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g) :=
  rfl

/-- **The sectionwise cotangent cohomology presheaf** `U ↦ H^i(L_{B(U)/A(U)})`: the cotangent
cohomology groups of the ring maps on sections, with the maps induced by the restriction
squares as restriction maps. -/
@[stacks 08SW "the presheaf U ↦ H^i(L_{B(U)/A(U)}); not its sheafification"]
noncomputable def sectionwiseCotangentCohomology (i : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  sectionwiseCotangentComplex J f ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) i

/-- The value of the sectionwise cotangent cohomology presheaf at `U` is `H^i(L_{B(U)/A(U)})`. -/
@[simp]
theorem sectionwiseCotangentCohomology_obj (i : ℤ) (U : Cᵒᵖ) :
    (sectionwiseCotangentCohomology J f i).obj U = (sectionsCotangentComplexAb J f U).homology i :=
  rfl

/-- The sectionwise cotangent cohomology presheaf is the composite of the sectionwise cotangent
complex with the `i`-th homology functor. -/
theorem sectionwiseCotangentCohomology_eq (i : ℤ) :
    sectionwiseCotangentCohomology J f i =
      sectionwiseCotangentComplex J f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) i :=
  rfl

end CategoryTheory.Sheaf

end
