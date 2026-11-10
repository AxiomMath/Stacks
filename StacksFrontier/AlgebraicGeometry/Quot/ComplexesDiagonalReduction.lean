module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic

/-!
# The reduction of the diagonal of `Complexes_{X/Y}` to a single test scheme

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, the standing
data of Stacks 0DLE, and let `x = (T, g, E)`, `y = (T, g', E')` be two objects of
`𝒳 = Complexes_{X/Y}` over the same scheme `T`. If for `h : T' ⟶ T` the restrictions `x|_{T'}`
and `y|_{T'}` are isomorphic, then `g ∘ h = g' ∘ h`; hence `Isom(x, y)` maps to
`Equalizer(g, g')`, which is a scheme because the diagonal of `Y` is representable.

So there are a monomorphism of schemes `j : Z ⟶ T`, through which every `T' ⟶ T` carrying a section
of `Isom(x, y)` factors, and two objects `(Z, j^*E)`, `(Z, j^*E')` of `𝒳` over the same test scheme
`Z ⟶ Y`, such that `Isom(x, y)` restricted to `(Sch/Z)` is `Isom((Z, j^*E), (Z, j^*E'))`. The
latter is computed by
`AlgebraicGeometry.Space.ComplexesSituation.complexesIsomPresheafIsoRelativeDerivedIsomFunctor`.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.fibreHom`: the morphism `T ⟶ Y` of an object of
  the fibre of `𝒳` over `T`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.map_comp_fibreHom_of_isHomLift`: a morphism of `𝒳`
  over `h : T' ⟶ T` relates the morphisms to `Y` of its source and target.
* `AlgebraicGeometry.Space.ComplexesSituation.exists_isomPresheaf_reduction`: `Isom(x, y)`
  restricted to the equalizer of `g` and `g'` is the `Isom` of two objects over the same test
  scheme.

## References

* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

/-- The morphism `T ⟶ Y` of an object of the fibre of `Complexes_{X/Y}` over `T`. -/
def fibreHom {U : BigFppfOver B S hS} (x : (complexesFunctor D).Fiber U) :
    (schemeSpaceFunctor B S hS).obj U ⟶ D.Y :=
  (schemeSpaceFunctor B S hS).map (eqToHom x.2.symm) ≫ x.1.T.hom

/-- A morphism of `Complexes_{X/Y}` lying over `h : V ⟶ W` relates the morphisms to `Y` of its
source and target: `g_a = g_b ∘ h`. -/
theorem map_comp_fibreHom_of_isHomLift {V W : BigFppfOver B S hS}
    (a : (complexesFunctor D).Fiber V) (b : (complexesFunctor D).Fiber W) (h : V ⟶ W)
    (φ : a.1 ⟶ b.1) (hφ : (complexesFunctor D).IsHomLift h φ) :
    (schemeSpaceFunctor B S hS).map h ≫ fibreHom b = fibreHom a := by
  obtain ⟨a, rfl⟩ := a
  obtain ⟨b, rfl⟩ := b
  have hf : (complexesFunctor D).map φ = h := by
    simpa using IsHomLift.fac' (complexesFunctor D) h φ
  have hw := CostructuredArrow.w (φ : ComplexesHom a b).base
  simp only [fibreHom, eqToHom_refl]
  rwa [← hf]

/-- **A section of `Isom(x, y)` over `h : T' ⟶ T` forces `g ∘ h = g' ∘ h`.** -/
theorem map_comp_fibreHom_eq_of_isomPresheaf {U : BigFppfOver B S hS}
    (x y : (complexesFunctor D).Fiber U) (g : Over U)
    (m : ((complexesFunctor D).isomPresheaf x y).obj (op g)) :
    (schemeSpaceFunctor B S hS).map g.hom ≫ fibreHom x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ fibreHom y := by
  have key (z) := map_comp_fibreHom_of_isHomLift
    (Functor.pullbackFiber (complexesFunctor D) z g.hom) z g.hom
    (Functor.IsPreFibered.pullbackMap z.2 g.hom) inferInstance
  have hm := map_comp_fibreHom_of_isHomLift (Functor.pullbackFiber (complexesFunctor D) x g.hom)
    (Functor.pullbackFiber (complexesFunctor D) y g.hom) (𝟙 g.left) m.1.1 m.1.2
  rw [key x, key y, ← hm, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The test scheme `Z ⟶ T ⟶ Y` of a morphism `j : Z ⟶ T` into the base of an object of the
fibre over `T`. -/
abbrev restrictTest {U Z : BigFppfOver B S hS} (x : (complexesFunctor D).Fiber U) (j : Z ⟶ U) :
    SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map j ≫ fibreHom x)

/-- The morphism of test schemes `(Z ⟶ T ⟶ Y) ⟶ (T ⟶ Y)` over `j`, when `j` equalises `g`
and `g'`. -/
def restrictTestHom {U Z : BigFppfOver B S hS} (x y : (complexesFunctor D).Fiber U) (j : Z ⟶ U)
    (hj : (schemeSpaceFunctor B S hS).map j ≫ fibreHom x =
      (schemeSpaceFunctor B S hS).map j ≫ fibreHom y) :
    restrictTest x j ⟶ y.1.T :=
  CostructuredArrow.homMk (j ≫ eqToHom y.2.symm) (by
    change _ = (schemeSpaceFunctor B S hS).map j ≫ fibreHom x
    rw [hj, fibreHom, CategoryTheory.Functor.map_comp, Category.assoc]
    rfl)

/-- The explicit pullback `(Z, j^*E)` of an object of the fibre over `T` along a morphism
`j : Z ⟶ T` equalising its morphism to `Y` with that of a second object. -/
abbrev restrictObject {U Z : BigFppfOver B S hS} (x y : (complexesFunctor D).Fiber U)
    (j : Z ⟶ U) (hj : (schemeSpaceFunctor B S hS).map j ≫ fibreHom x =
      (schemeSpaceFunctor B S hS).map j ≫ fibreHom y) : ComplexesObject D :=
  pullbackObject y.1 (restrictTestHom x y j hj)
    (relativelyPerfectBaseChange D _ y.1.E y.1.relativelyPerfect)

/-- The explicit pullback `(Z, j^*E)` lies over `j`, and is a cartesian lift of `j`. -/
theorem isHomLift_restrictObject {U Z : BigFppfOver B S hS} (x y : (complexesFunctor D).Fiber U)
    (j : Z ⟶ U) (hj : (schemeSpaceFunctor B S hS).map j ≫ fibreHom x =
      (schemeSpaceFunctor B S hS).map j ≫ fibreHom y) :
    (complexesFunctor D).IsHomLift j
      (pullbackHom y.1 (restrictTestHom x y j hj)
        (relativelyPerfectBaseChange D _ y.1.E y.1.relativelyPerfect) :
          restrictObject x y j hj ⟶ y.1) := by
  obtain ⟨y, rfl⟩ := y
  refine IsHomLift.of_fac _ _ _ rfl rfl ?_
  change j = 𝟙 _ ≫ (j ≫ eqToHom rfl)
  simp

/-- The isomorphism in the fibre over `Z` between the chosen pullback of `y` along `j` and the
explicit one. -/
def restrictFiberIso {U Z : BigFppfOver B S hS} (x y : (complexesFunctor D).Fiber U)
    (j : Z ⟶ U) (hj : (schemeSpaceFunctor B S hS).map j ≫ fibreHom x =
      (schemeSpaceFunctor B S hS).map j ≫ fibreHom y) :
    Functor.pullbackFiber (complexesFunctor D) y j ≅ ⟨restrictObject x y j hj, rfl⟩ := by
  haveI := isHomLift_restrictObject x y j hj
  haveI : (complexesFunctor D).IsStronglyCartesian j
      (pullbackHom y.1 (restrictTestHom x y j hj)
        (relativelyPerfectBaseChange D _ y.1.E y.1.relativelyPerfect) :
          restrictObject x y j hj ⟶ y.1) :=
    (complexesFunctor_isFiberedInGroupoids D).isStronglyCartesian_homLift j _
  let e := Functor.IsCartesian.domainUniqueUpToIso (complexesFunctor D) j
    (pullbackHom y.1 (restrictTestHom x y j hj)
      (relativelyPerfectBaseChange D _ y.1.E y.1.relativelyPerfect) :
        restrictObject x y j hj ⟶ y.1) (Functor.IsPreFibered.pullbackMap y.2 j)
  exact
    { hom := ⟨e.hom, inferInstance⟩
      inv := ⟨e.inv, inferInstance⟩
      hom_inv_id := Functor.Fiber.hom_ext e.hom_inv_id
      inv_hom_id := Functor.Fiber.hom_ext e.inv_hom_id }

/-- **`Isom(x, y)` over the equalizer of `g` and `g'`.** For objects `x = (T, g, E)` and
`y = (T, g', E')` of the fibre of `Complexes_{X/Y}` over `T`, the equalizer `j : Z ⟶ T` of `g` and
`g'` is a monomorphism of schemes through which every `T' ⟶ T` carrying a section of `Isom(x, y)`
factors, and `Isom(x, y)` restricted to `(Sch/Z)` is `Isom((Z, j^*E), (Z, j^*E'))`, for the two
explicit pullbacks over the same test scheme `Z ⟶ T ⟶ Y`; this in turn is the relative derived Isom
functor of `j^*E` and `j^*E'` along `X_Z ⟶ Z`. -/
theorem exists_isomPresheaf_reduction {U : BigFppfOver B S hS}
    (x y : (complexesFunctor D).Fiber U) :
    ∃ (Z : BigFppfOver B S hS) (j : Z ⟶ U) (_ : Mono j)
      (hj : (schemeSpaceFunctor B S hS).map j ≫ fibreHom x =
        (schemeSpaceFunctor B S hS).map j ≫ fibreHom y),
      (∀ g : Over U, Nonempty (((complexesFunctor D).isomPresheaf x y).obj (op g)) →
        ∃ t : g.left ⟶ Z, t ≫ j = g.hom) ∧
      Nonempty ((Over.map j).op ⋙ (complexesFunctor D).isomPresheaf x y ≅
        (overSchemeTest Z).op ⋙ relativeDerivedIsomFunctor
          (D.projection (restrictTest x j)) (restrictObject x x j rfl).E
          (restrictObject x y j hj).E) := by
  obtain ⟨Z, j, hmono, hiff⟩ := exists_mono_comp_eq_iff_factors (fibreHom x) (fibreHom y)
  have hj := (hiff j).2 ⟨𝟙 _, Category.id_comp _⟩
  refine ⟨Z, j, hmono, hj, fun g ⟨m⟩ => (hiff g.hom).1
    (map_comp_fibreHom_eq_of_isomPresheaf x y g m), ⟨?_⟩⟩
  exact (Stack.isomPresheafPullbackCompIso (complexesFunctor D) x y j).symm ≪≫
    Stack.isomPresheafIsoOfIso (complexesFunctor D) (restrictFiberIso x x j rfl)
      (restrictFiberIso x y j hj) ≪≫
    complexesIsomPresheafIsoRelativeDerivedIsomFunctor (restrictObject x x j rfl)
      (restrictObject x y j hj).E (restrictObject x y j hj).relativelyPerfect
      (restrictObject x y j hj).noNegativeFibreExt

end ComplexesSituation

end AlgebraicGeometry.Space

end
