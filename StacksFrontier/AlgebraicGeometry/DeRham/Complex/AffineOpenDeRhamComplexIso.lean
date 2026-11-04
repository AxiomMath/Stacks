module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamWedge

/-!
# The relative de Rham complex on an affine open is the algebraic one, as a complex

Let `f : X ⟶ S` be a morphism of schemes, let `U ⊆ X` and `V ⊆ S` be affine opens with
`U ≤ f^{-1}V`, and write `A := Γ(X, U)` and `R := Γ(S, V)`. The sections over `U` of the
relative de Rham complex of `f` are the algebraic de Rham complex `Ω^•_{A/R}`, as a cochain
complex:

`Γ(Ω^•_{X/S}, U) ≅ Ω^•_{A/R} = (⋀^•_A Ω[A⁄R], d)`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.sectionsAbFunctor`: sections over an open of a
  sheaf of `f^{-1}𝒪_S`-modules on `X`, as an abelian group.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplex`: `Γ(Ω^•_{X/S}, U)`, as a
  cochain complex of abelian groups.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAbComplex`: `Ω^•_{A/R}`, as a cochain
  complex of abelian groups.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.sectionsAbTermMap_comm`: **the degreewise
  comparison commutes with the de Rham differential**, in every degree.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplexIso`:
  **`Ω^•_{Γ(X,U)/Γ(S,V)} ≅ Γ(Ω^•_{X/S}, U)` as a cochain complex of abelian groups**, for affine
  opens `U ⊆ X` and `V ⊆ S` with `U ≤ f^{-1}V`.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplexIso_hom_f_apply`: its
  components are the degreewise comparison.

## Implementation notes

The de Rham differential is not `A`-linear, so the comparison is one of complexes of abelian
groups. The generators `a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` span the degree-`p` term over `ℤ`
(`Crystalline.span_range_smul_ιMulti_eq_top` at `R := ℤ`), so additive maps out of it are
determined by their values on them.

The sections functor is `SheafOfModules.toSheaf` followed by evaluation of the resulting abelian
sheaf at `U`, which lands in `AddCommGrpCat` with no restriction of scalars.

## References

* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

/-- Two additive maps out of an abelian group that agree on a set spanning it over `ℤ` are
equal. -/
theorem addMonoidHom_ext_of_span_int_eq_top {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {s : Set M} (hs : Submodule.span ℤ s = ⊤) {g h : M →+ N} (hgh : Set.EqOn g h s) : g = h :=
  AddMonoidHom.ext fun x ↦ LinearMap.congr_fun
    (LinearMap.ext_on (f := g.toIntLinearMap) (g := h.toIntLinearMap) hs hgh) x

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

/-- **Sections over an open `W` of a sheaf of `f^{-1}𝒪_S`-modules on `X`, as an abelian
group.** -/
def sectionsAbFunctor (W : X.Opens) :
    _root_.SheafOfModules.{u} (_root_.AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf _ ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op W)

/-- Sections over an open form an additive functor. -/
instance sectionsAbFunctor_additive (W : X.Opens) : (sectionsAbFunctor f W).Additive where
  map_add := rfl

/-- **`Γ(Ω^•_{X/S}, W)`, as a cochain complex of abelian groups**: the relative de Rham complex
of `f`, read on sections over the open `W` degree by degree. -/
def deRhamSectionsAbComplex (W : X.Opens) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sectionsAbFunctor f W).mapHomologicalComplex (ComplexShape.up ℕ)).obj f.deRhamComplex

/-- The arrows of the complex of sections are the de Rham differentials of `Ω^•_{X/S}`, read on
sections over `W`. -/
theorem deRhamSectionsAbComplex_d_apply (W : X.Opens) (p q : ℕ)
    (x : (deRhamSectionsAbComplex f W).X p) :
    ((deRhamSectionsAbComplex f W).d p q).hom x =
      ((f.deRhamComplex.d p q).val.app (op W)).hom x :=
  rfl

/-- **`Ω^•_{Γ(X,U)/Γ(S,V)}`, as a cochain complex of abelian groups**: the algebraic de Rham
complex of `f.appLE V U e`, with the module structure on its terms forgotten. -/
def ringDeRhamAbComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((forget₂ (ModuleCat.{u} ↥Γ(S, V)) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e))

/-- The arrows of the algebraic de Rham complex, read on an element after forgetting the module
structure, are the algebraic de Rham differentials. -/
theorem ringDeRhamAbComplex_d_apply (p q : ℕ) (x : (ringDeRhamAbComplex f e).X p) :
    ((ringDeRhamAbComplex f e).d p q).hom x =
      ((AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)).d p q).hom x :=
  rfl

include hU hV in
/-- **The degreewise comparison, as a map of abelian groups**: the degree-`p` term of
`Ω^•_{Γ(X,U)/Γ(S,V)}` maps to `Γ(Ω^p_{X/S}, U)` by
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`. -/
def sectionsAbTermMap (p : ℕ) :
    (ringDeRhamAbComplex f e).X p ⟶ (deRhamSectionsAbComplex f U).X p :=
  AddCommGrpCat.ofHom (formsSectionsIso f hU hV e p).inv.hom.toAddMonoidHom

include hU hV in
/-- The degreewise comparison of abelian groups is the inverse of the degreewise comparison of
`Γ(X, U)`-modules, read on an element. -/
theorem sectionsAbTermMap_apply (p : ℕ) (x : (ringDeRhamAbComplex f e).X p) :
    (sectionsAbTermMap f hU hV e p).hom x = (formsSectionsIso f hU hV e p).inv.hom x :=
  rfl

include hU hV in
/-- **The left-hand side of the de Rham square, unfolded.** The arrow of the complex of sections
applied to the degreewise comparison of abelian groups is the de Rham differential of
`Ω^•_{X/S}` over `U` applied to the degreewise comparison of `Γ(X, U)`-modules. -/
theorem deRhamSectionsAbComplex_d_sectionsAbTermMap (p : ℕ)
    (x : (ringDeRhamAbComplex f e).X p) :
    ((deRhamSectionsAbComplex f U).d p (p + 1)).hom ((sectionsAbTermMap f hU hV e p).hom x) =
      ((f.deRhamComplex.d p (p + 1)).val.app (op U)).hom
        ((formsSectionsIso f hU hV e p).inv.hom x) :=
  rfl

include hU hV in
/-- **The right-hand side of the de Rham square, unfolded.** The degreewise comparison of
abelian groups applied to an arrow of `Ω^•_{Γ(X,U)/Γ(S,V)}` is the degreewise comparison of
`Γ(X, U)`-modules applied to the algebraic de Rham differential. -/
theorem sectionsAbTermMap_ringDeRhamAbComplex_d (p : ℕ) (x : (ringDeRhamAbComplex f e).X p) :
    (sectionsAbTermMap f hU hV e (p + 1)).hom (((ringDeRhamAbComplex f e).d p (p + 1)).hom x) =
      (formsSectionsIso f hU hV e (p + 1)).inv.hom
        (((AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)).d p (p + 1)).hom x) :=
  rfl

include hU hV in
/-- The degreewise comparison of abelian groups is an isomorphism. -/
instance isIso_sectionsAbTermMap (p : ℕ) : IsIso (sectionsAbTermMap f hU hV e p) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (formsSectionsIso f hU hV e p).symm.toLinearEquiv.bijective

include hU hV in
/-- **The degree-`p` square of the affine-open de Rham comparison, for every `p`.** The
degreewise comparison carries the algebraic de Rham differential of `Ω^•_{Γ(X,U)/Γ(S,V)}` to the
de Rham differential of `Ω^•_{X/S}`, read on sections over `U`. -/
theorem sectionsAbTermMap_comm (p : ℕ) :
    sectionsAbTermMap f hU hV e p ≫ (deRhamSectionsAbComplex f U).d p (p + 1) =
      (ringDeRhamAbComplex f e).d p (p + 1) ≫ sectionsAbTermMap f hU hV e (p + 1) := by
  let := (f.appLE V U e).hom.toAlgebra
  refine AddCommGrpCat.hom_ext (addMonoidHom_ext_of_span_int_eq_top
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
      (KaehlerDifferential.D ↑Γ(S, V) ↑Γ(X, U))
      (KaehlerDifferential.span_range_derivation ↑Γ(S, V) ↑Γ(X, U)) p) ?_)
  rintro _ ⟨a, rfl⟩
  beta_reduce
  refine Eq.trans (deRhamSectionsAbComplex_d_sectionsAbTermMap f hU hV e p _) ?_
  refine Eq.trans ?_ (sectionsAbTermMap_ringDeRhamAbComplex_d f hU hV e p _).symm
  refine Eq.trans (deRhamComplex_d_formsSectionsIso f hU hV e p a) ?_
  exact congrArg (formsSectionsIso f hU hV e (p + 1)).inv.hom
    (KaehlerDifferential.deRhamComplex_d_smul_ιMulti_D p a).symm

include hU hV in
/-- **The relative de Rham complex on an affine open is the algebraic de Rham complex of its
sections**, for affine opens `U ⊆ X` and `V ⊆ S` with `U ≤ f^{-1}V`:

`Ω^•_{Γ(X,U)/Γ(S,V)} ≅ Γ(Ω^•_{X/S}, U)`

as a cochain complex of abelian groups, with components the degreewise comparison
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`. -/
def deRhamSectionsAbComplexIso : ringDeRhamAbComplex f e ≅ deRhamSectionsAbComplex f U :=
  HomologicalComplex.Hom.isoOfComponents (fun p ↦ asIso (sectionsAbTermMap f hU hV e p))
    (by rintro i _ rfl; exact sectionsAbTermMap_comm f hU hV e i)

include hU hV in
/-- **The complex-level comparison is the degreewise comparison in each degree.** -/
theorem deRhamSectionsAbComplexIso_hom_f_apply (p : ℕ) (x : (ringDeRhamAbComplex f e).X p) :
    ((deRhamSectionsAbComplexIso f hU hV e).hom.f p).hom x =
      (formsSectionsIso f hU hV e p).inv.hom x :=
  rfl

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
