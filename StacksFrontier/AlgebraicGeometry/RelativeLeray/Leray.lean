module

public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# The relative Leray spectral sequence, in the form of Stacks 015N

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces and let `K` be an object of
`D⁺(Mod(𝒪_X))`. Since `f_* ⋙ g_* = (f ≫ g)_*` on the nose
(`Stacks.RelativeLeray.modulePushforward_comp`) and `f_*` carries injective modules to
`g_*`-acyclic modules (`Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective`),
the Grothendieck spectral sequence of [Stacks, Tag 015N] applies to the pair `(f_*, g_*)` and
produces a spectral sequence
```
E_2^{p,q} = R ᵖ g_*(H^q(R f_* K))
```
which is bounded, converges to `H ⁎(R (f ≫ g)_* K)` and induces a finite filtration on each
`H ⁿ(R (f ≫ g)_* K)`.

This is the mathematical content of [Stacks, Tag 01F6], in the presentation [Stacks, Tag 015N]
delivers it: a filtered complex together with the identification of its pages by the
subquotients `Z_r^{p,q}/D_r^{p,q}` of [Stacks, Tag 012M]. **It is not the statement of Tag
01F6 itself**, which asks for the spectral sequence as a *functor* of the module, carried on
`ℕ × ℕ` from the second page, with a functorial filtered abutment whose graded pieces are the
infinity page; see the implementation notes for exactly what separates the two, and
`StacksFrontier.AlgebraicGeometry.RelativeLeray.Statement` for the target shape. Nothing here
carries the tag `01F6`.

## Main results

* `Stacks.RelativeLeray.exists_spectralSequence_relativeLeray`: the relative Leray spectral
  sequence `R ᵖ g_*(H^q(R f_* K)) ⇒ H^{p+q}(R (f ≫ g)_* K)` for a bounded below complex of
  `𝒪_X`-modules.
* `Stacks.RelativeLeray.homologyFunctor_rightDerivedFunctorPlus_single`: the second page of
  that sequence at `K = F[0]` is `R ᵖ g_*(R^q f_* F)`, the identification being an equality of
  objects rather than an isomorphism.

## Implementation notes

* As for [Stacks, Tag 015N] and [Stacks, Tag 0132], a spectral sequence "converging to
  `H ⁎(L)`" is a spectral sequence together with a filtered complex `L` whose spectral sequence
  it is: its pages are identified with the quotients `Z_r^{p,q}/D_r^{p,q}` of
  [Stacks, Tag 012M], and boundedness, finiteness of the filtration `F ᵖH ⁿ(L)` induced on
  cohomology and convergence are properties of that presentation. The subobjects `F ᵖL ⁿ`,
  `Z_r^{p,q}`, `D_r^{p,q}` and `F ᵖH ⁿ(L)` are quantified together with their defining
  equations, as in [Stacks, Tag 012W].
* The abutment needs no comparison isomorphism. `modulePushforward_comp` is an equality of
  functors proved by `rfl`, so `(f_* ⋙ g_*).rightDerivedFunctorPlus` and
  `(f ≫ g)_*.rightDerivedFunctorPlus` are the same functor and the conclusion of
  [Stacks, Tag 015N] may be *stated* about the composite morphism directly.
* The module version is the complex version evaluated at `F[0]`, and needs no comparison
  isomorphism either: `R^q f_*` *is* `F ↦ H^q(R f_*(F[0]))` by the definition of
  `CategoryTheory.Functor.rightDerivedPlus`, so the two readings of the second page are equal
  objects (`homologyFunctor_rightDerivedFunctorPlus_single`). What the tag still asks for
  beyond this is `R^q f_*` in Mathlib's `ℕ`-indexed spelling `Functor.rightDerived`, for which
  `Stacks.DerivedIndexing.rightDerivedIso` is the comparison.
* What this statement does **not** provide, and [Stacks, Tag 01F6] asks for: the spectral
  sequence is produced one object at a time (so it is not a functor on `Mod(𝒪_X)`), it is
  carried on `ℤ × ℤ` from page `0` rather than on `ℕ × ℕ` from page `2`, the page-two
  identification and the abutment comparison are `Nonempty`-valued (so no naturality can even
  be asked of them), and the filtration of the abutment is given by the subobjects `F ᵖH ⁿ(L)`
  with no identification of its graded pieces with the infinity page. Three of those four are
  avoided altogether by the other route to the same spectral sequence,
  `StacksFrontier.AlgebraicGeometry.RelativeLeray.SpectralObject`, which builds it from the
  truncation tower rather than from a resolution; this statement is kept because it is the one
  that comes with boundedness and convergence of the filtration.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeLeray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! The lattice structure on subobjects of a sheaf of modules, which the presentation of the
pages by `Z_r^{p,q}/D_r^{p,q}` uses. Each of these is found by `inferInstance` on its own, but
not from inside the statement below, where the search is nested several classes deep; they are
named here so that the statement elaborates. -/

/-- The category of sheaves of modules on a ringed space has images. -/
local instance hasImages_modules (X : RingedSpace.{u, u}) :
    HasImages (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

/-- The category of sheaves of modules on a ringed space has binary coproducts. -/
local instance hasBinaryCoproducts_modules (X : RingedSpace.{u, u}) :
    HasBinaryCoproducts (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

/-- The category of sheaves of modules on a ringed space has an initial object. -/
local instance hasInitial_modules (X : RingedSpace.{u, u}) :
    HasInitial (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

/-- In the category of sheaves of modules on a ringed space, every morphism out of an initial
object is a monomorphism. -/
local instance initialMonoClass_modules (X : RingedSpace.{u, u}) :
    InitialMonoClass (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

/-- The category of sheaves of modules on a ringed space has pullbacks. -/
local instance hasPullbacks_modules (X : RingedSpace.{u, u}) :
    HasPullbacks (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The relative Leray spectral sequence.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
ringed spaces and let `K` be an object of `D⁺(Mod(𝒪_X))`. There is a filtered complex `L` of
`𝒪_Z`-modules with `H ⁿ(L) ≅ H ⁿ(R (f ≫ g)_* K)` for all `n`, whose filtration is finite in
each degree and whose spectral sequence `E`, presented as in [Stacks, Tag 012M] by its pages
`Z_r^{p,q}/D_r^{p,q}`, has `E_2^{p,q} ≅ R ᵖ g_*(H^q(R f_* K))`, is bounded, induces a finite
filtration on each `H ⁿ(L)`, and converges to `H ⁎(L)`.

Degreewise finiteness of the filtration of `L` is carried as a conclusion because it is the
sole hypothesis of the abutment statements, notably of
`CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`
([Stacks, Tag 01F2]): a consumer that wants abutment of `E` to
`H ⁎(L)` rather than the raw convergence equalities below needs exactly this and nothing
else.

This is [Stacks, Tag 015N] for the composition `(f ≫ g)_* = g_* ∘ f_*`, whose hypothesis is
`rightAcyclic_modulePushforward_obj_injective`. It is the mathematical content of
[Stacks, Tag 01F6] and not its statement; see the implementation notes of this file. -/
theorem exists_spectralSequence_relativeLeray
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ L : FilteredObject (CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (L.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) n).obj
          ((modulePushforward (f ≫ g)).rightDerivedFunctorPlus.obj K))) ∧
      L.filtration.IsDegreewiseFinite ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((L.filtration.ι.app (op p)).f n))
        (Zc : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, Zc r p n =
          Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (Dc : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, Dc r p n = Zc (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (L.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (L.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (L.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : Dc r p n ⊓ Zc r p n ≤ Zc r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          ((modulePushforward g).rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing Y)) q).obj
              ((modulePushforward f).rightDerivedFunctorPlus.obj K)))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (L.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (L.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (L.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) :=
  CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp
    (modulePushforward f) (modulePushforward g)
    (fun I _ => rightAcyclic_modulePushforward_obj_injective f g I) K

/-- **The second page of the relative Leray spectral sequence at a single module.** Evaluating
`exists_spectralSequence_relativeLeray` at `K = F[0]` turns `H^q(R f_* K)` into `R^q f_* F`,
and does so on the nose: the higher direct image is *defined* as the degree-`q` cohomology of
the derived pushforward of the complex concentrated in degree zero. -/
theorem homologyFunctor_rightDerivedFunctorPlus_single
    (F : SheafOfModules.{u} (structureSheafRing X)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).obj
        ((modulePushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            F)) =
      ((modulePushforward f).rightDerivedPlus q).obj F :=
  rfl

end Stacks.RelativeLeray

end
