module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a short exact sequence of finite locally free sheaves

Let `(X, O_X)` be a ringed space and let `E' --f--> E --g--> E''` be an exact sequence of
sheaves of `O_X`-modules with `g` an epimorphism and `E'` finite locally free of constant rank
`r'`. For a sheaf of modules which is finite locally free of constant rank `r` the determinant
of [Stacks, Tag 0B37] is the top exterior power `⋀ʳ`, so in that situation the canonical
isomorphism of [Stacks, Tag 0B38] reads

`⋀^{r'}(E') ⊗_{O_X} ⋀^{r''}(E'') ⟶ ⋀^{r' + r''}(E)`.

**This file constructs that comparison morphism and proves the wedge-and-lift equation that
makes it canonical.** The construction is the one the source describes: the map sends
`(s₁ ∧ ⋯ ∧ s_{r'}) ⊗ (t₁ ∧ ⋯ ∧ t_{r''})` to `f(s₁) ∧ ⋯ ∧ f(s_{r'}) ∧ l₁ ∧ ⋯ ∧ l_{r''}`, where
`lⱼ` is any local lift of `tⱼ` along `g`; the value is independent of the lifts because
`⋀^{r'+1}(E') = 0`.

## Main definitions

* `Stacks.SheafOfModules.TopWedge.wedgeHom`: the wedge map `⋀ʳ E' ⊗ ⋀ˢ E ⟶ ⋀ʳ⁺ˢ E`, which needs
  no lifting because it multiplies in the exterior algebra of `E`.
* `Stacks.SheafOfModules.TopWedge.detComparison`: **the canonical comparison**
  `⋀^{r'} E' ⊗ ⋀^{k+1} E'' ⟶ ⋀^{r'+k+1} E`, obtained by descending `wedgeHom` along the
  presentation `E' ⊗ ⋀ᵏ E ⟶ ⋀ᵏ⁺¹ E ⟶ ⋀ᵏ⁺¹ E'' ⟶ 0` of [Stacks, Tag 01CJ]: that presentation
  stays a presentation after tensoring with `⋀^{r'} E'`, because the tensor product of sheaves of
  modules is right exact.
* `Stacks.SheafOfModules.TopWedge.wedgeSec`: the wedge `t₀ ∧ ⋯ ∧ t_{n-1}` of local sections,
  as a local section of `⋀ⁿ`.

## Main results

* `Stacks.SheafOfModules.TopWedge.detComparison_wedge`: **the wedge-and-lift formula**, the
  equation that pins the comparison down.
* `Stacks.SheafOfModules.TopWedge.detComparison_unit` and
  `Stacks.SheafOfModules.TopWedge.tensorLeftMap_comp_detComparison`: the same equation in the
  form the construction produces, on local sections and as an equality of morphisms.
* `Stacks.SheafOfModules.TopWedge.eq_detComparison`: the comparison is the **only** morphism
  satisfying that equation, since the morphism it is characterized against is an epimorphism.
* `Stacks.SheafOfModules.TopWedge.wedgeHom_tensorLeftMap_relComplex_f`: the wedge map kills the
  relation of Tag 01CJ, which is what lets it descend. This is where the top exterior power of
  `E'` is used.
* `Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt`: the exterior powers of a finite
  locally free sheaf of modules above its rank have only the zero section.
* `Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp`: the stalks of a sheaf of
  modules which is finite locally free of rank `r` on a ringed space are free of rank `r`.

## Implementation notes

**Why this is a statement about determinants.** That the determinant of Tag 0FJN — the
annihilator of the degree-one part of the exterior algebra — *is* the top exterior power for a
sheaf of modules of constant rank `r` is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower`, as
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`. The comparison
below can therefore be read as a map `det(E') ⊗ det(E'') ⟶ det(E)` in the constant-rank case.

**What is not covered.** One clause of Tag 0B38 is not proved, and the attribute descriptions
say so: `E'` is assumed finite locally free of *constant* rank `r'` and the second degree is
written `r'' = k + 1`, whereas the source assumes only that the three sheaves are finite locally
free. The general case is not performed here. It does **not** need the clopen rank decomposition
of Tag 0B37: the constant rank of `E'` is used only through
`Stacks.SheafOfModules.TopWedge.mul_extHom_generator_eq_zero`, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact` isolates that use
as a hypothesis and discharges it, with no rank hypothesis, for the determinant summands of
Tag 0FJN; what remains of the general case is recorded there. That the comparison constructed
here is an **isomorphism** is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso`, as
`Stacks.SheafOfModules.TopWedge.isIso_detComparison`.

**The isomorphism clause needs `E''` finite locally free too, and that is not a weakening.**
Tag 0B38 assumes all three of `E'`, `E` and `E''` finite locally free, and the isomorphism
clause is false without the hypothesis on `E''`, even granted constant ranks for `E'` and `E`.
Take `X` a point with `O_X` a discrete valuation ring, uniformizer `p`, and the short exact
sequence with `E' = O_X`, `E = O_X²`, `f` the injection `1 ↦ (p, 0)`, and `E''` the cokernel;
then `E'` is free of rank `1` and `E` is free of rank `2 = r' + (k + 1)` with `r' = k + 1 = 1`,
but `E''` is not free of rank `1`. Every value of the wedge-and-lift formula there is
`(p, 0) ∧ (a, b) = pb · (e₁ ∧ e₂)`, so the image of the comparison is `p · ⋀²E ⊊ ⋀²E` and the
comparison is not even an epimorphism. This is why `isIso_detComparison` carries
`IsFiniteLocallyFreeOfRank E'' (k + 1)` alongside the hypothesis on `E'`, and `Mono f`.

**The isomorphism clause does not go through the algebraic `γ` of Tag 0FJB.** With the ranks of
`E'` and `E''` in hand, the source and the target of the comparison have rank
`binom(n, n) = 1`, so each stalk of each is free of rank one over the local ring; a surjection
between free modules of rank one over a commutative ring is injective by the Orzech property, so
only **surjectivity** on stalks has to be proved. That is done by exhibiting the wedge of a
basis of `E_x` in the image, using that the stalk sequence splits because `E''_x` is free. The
comparison with `ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact` — which would
need the multiplicativity of the comparison of Tag 01CH in two arbitrary degrees, where this
library has it only against a degree-one factor — is therefore avoided entirely. The details are
in the implementation notes of the file named above.

**Why the presentation of Tag 01CJ and not a direct definition.** A morphism out of
`⋀^{r'} E' ⊗ ⋀^{r''} E''` is the same thing as a bilinear map of the underlying presheaves, and
no such bilinear map exists: the value on `ω ⊗ t` needs a lift of `t` along `g`, which exists
only locally. The lifting is therefore not performed by hand; instead the wedge map out of
`⋀^{r'} E' ⊗ ⋀^{r''} E`, which needs no lift, is shown to kill the relations of the presentation
and descend. The lift in the formula `detComparison_wedge` is then an arbitrary local section
`l` of `E` whose image is the given section of `E''`, exactly as the source says.

**Multiplication is computed in the ungraded realization.** The multiplication of a sheaf of
graded algebras records associativity as an `HEq` between values at arbitrary local sections, so
the computations below are carried out in `Stacks.GradedAlgebra.Total`, an honest ring, and
transported back along the injective `Stacks.GradedAlgebra.incl`.

**No choice of data out of an existence statement.** `detComparison` is the `IsColimit.desc` of
the wedge map against the tensored presentation; the colimit witness is
`CategoryTheory.ShortComplex.Exact.gIsCokernel` applied to Tag 01CJ, not a chosen isomorphism.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 0FJB](https://stacks.math.columbia.edu/tag/0FJB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.TopWedge

/-! ### Ordered products of degree-one local sections -/

section ProdLemmas

variable {C : Type u} [Category.{u} C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}
  {Pc : ℤ → PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}

/-- Postcomposing a concatenation of families with a function concatenates the postcomposed
families. -/
private theorem comp_fin_append {α β : Type*} (h : α → β) {m n : ℕ} (z : Fin m → α)
    (w : Fin n → α) :
    (fun i => h (Fin.append z w i)) = Fin.append (fun i => h (z i)) fun i => h (w i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- **The ordered product of degree-one sections is multiplicative in concatenation.** The
product of the wedge of `s` with the wedge of `t` is the wedge of the concatenated family. -/
theorem homogeneousProd_append (B : Stacks.GradedAlgebra Pc) (U : Cᵒᵖ) (m n : ℕ)
    (s : Fin m → (Pc 1).obj U) (t : Fin n → (Pc 1).obj U) :
    (B.mul (m : ℤ) (n : ℤ)).app U (B.homogeneousProd U m s) (B.homogeneousProd U n t) =
      B.homogeneousProd U (m + n) (Fin.append s t) := by
  refine B.incl_inj_of_proj (i := ((m + n : ℕ) : ℤ)) ?_
  refine Eq.trans (B.incl_mul_incl (m : ℤ) (n : ℤ) (B.homogeneousProd U m s)
    (B.homogeneousProd U n t)).symm ?_
  refine Eq.trans ?_ (B.incl_homogeneousProd U (m + n) (Fin.append s t)).symm
  rw [B.incl_homogeneousProd U m s, B.incl_homogeneousProd U n t,
    comp_fin_append (B.incl 1) s t, List.ofFn_fin_append,
    List.prod_append]

end ProdLemmas

section UnitalHomProd

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {B D : _root_.SheafOfModules.GradedAlgebra.{u, u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The ordered product of `n` degree-one local sections of a sheaf of graded algebras: the
wedge `z₀ ∧ ⋯ ∧ z_{n-1}` when the algebra is an exterior algebra. -/
noncomputable abbrev wedgeProd
    (B : _root_.SheafOfModules.GradedAlgebra.{u, u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (U : (Opens ↥X)ᵒᵖ) (n : ℕ) (z : Fin n → (B.piece 1).val.obj U) :
    (B.piece (n : ℤ)).val.obj U :=
  Stacks.GradedAlgebra.homogeneousProd (Pc := fun i => (B.piece i).val)
    B.toPresheafGradedAlgebra U n z

/-- A unital homomorphism of sheaves of graded algebras carries the ordered product of
degree-one local sections to the ordered product of their images. -/
theorem unitalHom_homogeneousProd (φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom B D)
    (U : (Opens ↥X)ᵒᵖ) (n : ℕ) (z : Fin n → (B.piece 1).val.obj U) :
    (φ.app (n : ℤ)).val.app U (wedgeProd B U n z) =
      wedgeProd D U n fun i => (φ.app 1).val.app U (z i) := by
  induction n with
  | zero =>
      change (φ.app 0).val.app U (B.one.eval U) = D.one.eval U
      exact φ.map_one U
  | succ n ih =>
      change (φ.app ((n : ℤ) + 1)).val.app U
            ((B.mul (n : ℤ) 1).app U
              (wedgeProd B U n fun i => z i.castSucc)
              (z (Fin.last n))) =
          (D.mul (n : ℤ) 1).app U
            (wedgeProd D U n fun i => (φ.app 1).val.app U (z i.castSucc))
            ((φ.app 1).val.app U (z (Fin.last n)))
      rw [φ.map_mul (n : ℤ) 1 U, ih]

end UnitalHomProd

/-! ### The stalks of a finite locally free sheaf of modules -/

section StalkFree

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf

/-- The trivialisation of a locally free sheaf of modules carried by a member of its
local-generator data: on `q.X i` the restriction of `F` is the free sheaf on the index type of
the `i`-th family of generators. -/
noncomputable def trivializationOfGenerators
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} F) (hq : q.IsLocallyFreeData) (i : q.I) :
    LocallyFreeRank.Trivialization X (LocallyFreeRank.toRingSheaf X Osharp) F (q.X i) := by
  have hiso : IsIso (q.generators i).π := hq.isIso i
  refine ⟨(q.generators i).I, ?_⟩
  exact (_root_.SheafOfModules.mapFreeIso ((q.X i).sheafOfModulesEquivOver
        (LocallyFreeRank.toRingSheaf X Osharp)).functor (q.generators i).I
      ((q.X i).sheafOfModulesEquivOverUnit (LocallyFreeRank.toRingSheaf X Osharp)) ≪≫
    ((q.X i).sheafOfModulesEquivOver (LocallyFreeRank.toRingSheaf X Osharp)).functor.mapIso
      (@asIso _ _ _ _ (q.generators i).π hiso)).symm

/-- **The stalks of a finite locally free sheaf of modules of rank `r` are free of rank `r`.**
A member of the local-generator data through the point trivialises `F` there, and the index type
of that trivialisation is equivalent to `Fin r`. -/
theorem nonempty_stalkLinearEquiv_finsupp
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (r : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : ↥X) :
    Nonempty (↑(TopCat.Presheaf.stalk F.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) := by
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]
    trivial
  rw [Opens.mem_iSup] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X Osharp F x hi
    (trivializationOfGenerators F q hq i)
  exact ⟨e.trans (Finsupp.domLCongr (hr i).some)⟩

/-- A sheaf of modules all of whose stalks have a single element is a zero object: its identity
is the zero morphism. -/
theorem id_eq_zero_of_subsingleton_stalk
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (h : ∀ x : ↥X, Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    (𝟙 F : F ⟶ F) = 0 := by
  have hmono : Mono (0 : F ⟶ F) := by
    rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
    intro x a b _
    exact (h x).elim a b
  exact (cancel_mono (0 : F ⟶ F)).1 (by rw [Category.id_comp, Limits.zero_comp])

/-- **The exterior powers of a finite locally free sheaf of modules above its rank vanish.**
The degree-`n` exterior power of a sheaf of modules of rank `r` is finite locally free of rank
`binom(r, n)`, which is zero for `n > r`, so all its stalks vanish and so do all its sections. -/
@[ega "0 5.5.4" "partial", sga "6 VII 4.1" "partial"]
theorem exteriorPower_eq_zero_of_lt
    {E' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E') (r n : ℕ) (hrn : r < n)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (U : (Opens ↥X)ᵒᵖ) (z : (A'.exteriorPower n).val.obj U) : z = 0 := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (A'.exteriorPower n) 0 := by
    have h := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower A' r n
    rwa [Nat.choose_eq_zero_of_lt hrn] at h
  have hsub : ∀ x : ↥X,
      Subsingleton ↑(TopCat.Presheaf.stalk (A'.exteriorPower n).val.presheaf x) := by
    intro x
    obtain ⟨e⟩ := nonempty_stalkLinearEquiv_finsupp (A'.exteriorPower n) 0 x
    have : Subsingleton (Fin 0 →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x)) :=
      ⟨fun a b => Finsupp.ext fun i => i.elim0⟩
    exact e.toEquiv.subsingleton
  calc z = (𝟙 (A'.exteriorPower n) : _ ⟶ _).val.app U z := rfl
    _ = (0 : A'.exteriorPower n ⟶ A'.exteriorPower n).val.app U z := by
        rw [id_eq_zero_of_subsingleton_stalk (A'.exteriorPower n) hsub]
    _ = 0 := rfl

end StalkFree

/-! ### The wedge map -/

section Wedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (f : E' ⟶ E)

/-- The homomorphism of exterior algebras induced by a morphism of sheaves of modules. -/
noncomputable abbrev extHom : _root_.SheafOfModules.GradedAlgebra.UnitalHom A'.exterior
    A.exterior :=
  A'.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra f

/-- The induced homomorphism of exterior algebras extends `f` in degree one. -/
theorem extHom_app_one (V : (Opens ↥X)ᵒᵖ) (a : E'.val.obj V) :
    ((extHom A' A f).app 1).val.app V (A'.exteriorGenerator.val.app V a) =
      A.exteriorGenerator.val.app V (f.val.app V a) :=
  congrArg (fun m : E' ⟶ A.exterior.piece 1 => m.val.app V a)
    (_root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one
      A'.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra f)

/-- Wedging a local section of `⋀ʳ E'` into `⋀ʳ E` against a local section of `⋀ˢ E`, as a
bilinear map of the underlying presheaves of modules. -/
noncomputable def wedgeBilinear (r s : ℕ) :
    Stacks.BilinearMap (A'.exteriorPower r).val (A.exteriorPower s).val
      (A.exteriorPower (r + s)).val :=
  (A.exterior.mul (r : ℤ) (s : ℤ)).compLeft ((extHom A' A f).app (r : ℤ)).val

/-- **The wedge map `⋀ʳ E' ⊗ ⋀ˢ E ⟶ ⋀ʳ⁺ˢ E`**: the image of a local section of `⋀ʳ E'` in
`⋀ʳ E`, multiplied by a local section of `⋀ˢ E`. -/
noncomputable def wedgeHom (r s : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)).obj
        (A.exteriorPower s) ⟶
      A.exteriorPower (r + s) :=
  PresheafOfModules.tensorSheafDesc (F := A'.exteriorPower r) (G := A.exteriorPower s)
    (Q := A.exteriorPower (r + s)) (PresheafOfModules.ofBilinear (wedgeBilinear A' A f r s))

/-- The wedge map on the image of a pure tensor of local sections. -/
theorem wedgeHom_unit (r s : ℕ) (U : (Opens ↥X)ᵒᵖ) (x : (A'.exteriorPower r).val.obj U)
    (y : (A.exteriorPower s).val.obj U) :
    (wedgeHom A' A f r s).val.app U
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r) (A.exteriorPower s)).app U
          (x ⊗ₜ y)) =
      (A.exterior.mul (r : ℤ) (s : ℤ)).app U
        (((extHom A' A f).app (r : ℤ)).val.app U x) y :=
  (PresheafOfModules.tensorSheafDesc_unit _ U x y).trans
    ((PresheafOfModules.ofBilinear_tmul (wedgeBilinear A' A f r s) U x y).trans
      (Stacks.BilinearMap.compLeft_app (A.exterior.mul (r : ℤ) (s : ℤ))
        ((extHom A' A f).app (r : ℤ)).val U x y))

end Wedge

/-! ### Bilinear maps and local surjectivity in the second variable -/

section BilinearRight

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {Rp : Cᵒᵖ ⥤ RingCat.{u}}
  {M N N' P : PresheafOfModules.{u} Rp}

/-- A bilinear map into a separated presheaf of modules is determined by its restriction along
a locally surjective morphism in the **second** variable. This is
`Stacks.BilinearMap.app_eq_of_isLocallySurjective` read through `Stacks.BilinearMap.flip`. -/
theorem bilinear_app_eq_of_isLocallySurjective_right
    (hP : Presheaf.IsSeparated J P.presheaf) (α : N ⟶ N')
    [PresheafOfModules.IsLocallySurjective J α] (β₁ β₂ : Stacks.BilinearMap M N' P)
    (h : ∀ (V : Cᵒᵖ) (x : M.obj V) (y : N.obj V),
      β₁.app V x (α.app V y) = β₂.app V x (α.app V y))
    (V : Cᵒᵖ) (a : M.obj V) (b : N'.obj V) : β₁.app V a b = β₂.app V a b :=
  Stacks.BilinearMap.app_eq_of_isLocallySurjective hP α β₁.flip β₂.flip
    (fun W y x => h W x y) V b a

end BilinearRight

section HomExtRight

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{u}}
  {Fp Gp Hp Tp Qp : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- Two morphisms out of a twice-iterated objectwise tensor product of presheaves of modules
which agree on the triple pure tensors `x ⊗ₜ (y ⊗ₜ z)` of local sections are equal. This is the
mirror of `PresheafOfModules.tensorObj_hom_ext₂`. -/
theorem tensorObj_hom_ext₂_right
    {φ ψ : PresheafOfModules.tensorObj Fp (PresheafOfModules.tensorObj Gp Hp) ⟶ Qp}
    (h : ∀ (V : Cᵒᵖ) (x : Fp.obj V) (y : Gp.obj V) (z : Hp.obj V),
      PresheafOfModules.Hom.app φ V (x ⊗ₜ (y ⊗ₜ z)) =
        PresheafOfModules.Hom.app ψ V (x ⊗ₜ (y ⊗ₜ z))) :
    φ = ψ :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (TensorProduct.ext_threefold' (h V))

/-- Two morphisms out of `Fp ⊗ Tp` agreeing on the pure tensors `x ⊗ₜ η (y ⊗ₜ z)` are equal,
provided the target is separated and `η : Gp ⊗ Hp ⟶ Tp` is locally surjective. This is the
mirror of `PresheafOfModules.tensorObj_hom_ext_of_isLocallySurjective`. -/
theorem tensorObj_hom_ext_of_isLocallySurjective_right
    (hQ : Presheaf.IsSeparated J Qp.presheaf)
    (η : PresheafOfModules.tensorObj Gp Hp ⟶ Tp)
    [PresheafOfModules.IsLocallySurjective J η]
    {φ ψ : PresheafOfModules.tensorObj Fp Tp ⟶ Qp}
    (h : ∀ (V : Cᵒᵖ) (x : Fp.obj V) (y : Gp.obj V) (z : Hp.obj V),
      PresheafOfModules.Hom.app φ V (x ⊗ₜ PresheafOfModules.Hom.app η V (y ⊗ₜ z)) =
        PresheafOfModules.Hom.app ψ V (x ⊗ₜ PresheafOfModules.Hom.app η V (y ⊗ₜ z))) :
    φ = ψ := by
  have key : PresheafOfModules.ofBilinear ((PresheafOfModules.toBilinear φ).compRight η) =
      PresheafOfModules.ofBilinear ((PresheafOfModules.toBilinear ψ).compRight η) :=
    tensorObj_hom_ext₂_right fun V x y z => h V x y z
  refine PresheafOfModules.tensorObj_hom_ext fun V x t => ?_
  refine bilinear_app_eq_of_isLocallySurjective_right hQ η (PresheafOfModules.toBilinear φ)
    (PresheafOfModules.toBilinear ψ) (fun W a y => ?_) V x t
  exact PresheafOfModules.hom_congr_apply' key W (a ⊗ₜ y)

end HomExtRight

section SheafHomExtRight

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {F G H Q : _root_.SheafOfModules.{u} (toRingCat J Osharp)}

/-- **Two morphisms out of `F ⊗ (G ⊗ H)` agreeing on the images of the nested pure tensors of
local sections are equal.** This is the mirror of
`PresheafOfModules.tensorSheaf_hom_ext₂`, with the iterated tensor product on the right. -/
theorem tensorSheaf_hom_ext_right
    {φ ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj F).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj G).obj H) ⟶ Q}
    (h : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V) (z : H.val.obj V),
      φ.val.app V ((PresheafOfModules.tensorSheafUnit F
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj G).obj H)).app V
            (x ⊗ₜ (PresheafOfModules.tensorSheafUnit G H).app V (y ⊗ₜ z))) =
        ψ.val.app V ((PresheafOfModules.tensorSheafUnit F
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj G).obj H)).app V
            (x ⊗ₜ (PresheafOfModules.tensorSheafUnit G H).app V (y ⊗ₜ z)))) :
    φ = ψ := by
  have hls : PresheafOfModules.IsLocallySurjective J
      (PresheafOfModules.tensorSheafUnit G H) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (𝟙 (toRingCat J Osharp).obj) (PresheafOfModules.tensorObj G.val H.val)
  refine PresheafOfModules.tensorSheaf_hom_ext fun U x t => ?_
  exact PresheafOfModules.hom_congr_apply'
    (tensorObj_hom_ext_of_isLocallySurjective_right Q.isSheaf.isSeparated
      (PresheafOfModules.tensorSheafUnit G H)
      (φ := PresheafOfModules.tensorSheafUnit F
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj G).obj H) ≫ φ.val)
      (ψ := PresheafOfModules.tensorSheafUnit F
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj G).obj H) ≫ ψ.val)
      h) U (x ⊗ₜ t)

end SheafHomExtRight

/-! ### The relation killed by the wedge map -/

section Vanishing

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)

/-- The three-term complex of [Stacks, Tag 01CJ] for the presentation `E' → E → E''` in degree
`k + 1`: `E' ⊗ ⋀ᵏ E ⟶ ⋀ᵏ⁺¹ E ⟶ ⋀ᵏ⁺¹ E''`. -/
noncomputable abbrev relComplex (k : ℕ) :
    ShortComplex (_root_.SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  _root_.SheafOfModules.ExtPresentation.extComplex A.exteriorGenerator A''.exteriorGenerator
    A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g f hfg k

/-- The second map of the complex of Tag 01CJ is the exterior power of `g`. -/
theorem relComplex_g (k : ℕ) :
    (relComplex A A'' f g hfg k).g = (extHom A A'' g).app ((k + 1 : ℕ) : ℤ) := rfl

/-- The wedge of the image of a top local section of `⋀ʳ' E'` with a degree-one generator
coming from `E'` vanishes: it is the image of a local section of `⋀ʳ'⁺¹ E' = 0`. -/
theorem mul_extHom_generator_eq_zero
    (r' : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (V : (Opens ↥X)ᵒᵖ) (ω : (A'.exteriorPower r').val.obj V) (a : E'.val.obj V) :
    (A.exterior.mul (r' : ℤ) 1).app V (((extHom A' A f).app (r' : ℤ)).val.app V ω)
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0 := by
  have hz : (A'.exterior.mul (r' : ℤ) 1).app V ω (A'.exteriorGenerator.val.app V a) = 0 :=
    exteriorPower_eq_zero_of_lt A' r' (r' + 1) (by omega) V _
  refine Eq.trans (congrArg
    ((A.exterior.mul (r' : ℤ) 1).app V (((extHom A' A f).app (r' : ℤ)).val.app V ω))
    (extHom_app_one A' A f V a).symm) ?_
  refine Eq.trans ((extHom A' A f).map_mul (r' : ℤ) 1 V ω
    (A'.exteriorGenerator.val.app V a)).symm ?_
  exact Eq.trans (congrArg (((extHom A' A f).app ((r' : ℤ) + 1)).val.app V) hz) (map_zero _)

/-- The tensor product `F ⊗ -` on a morphism `u`, computed on the image of a local pure tensor. -/
private theorem tensorLeftMap_unit
    {F P Q : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (u : P ⟶ Q) (V : (Opens ↥X)ᵒᵖ) (ω : F.val.obj V) (x : P.val.obj V) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj F).map u).val.app V
        ((PresheafOfModules.tensorSheafUnit F P).app V (ω ⊗ₜ x)) =
      (PresheafOfModules.tensorSheafUnit F Q).app V (ω ⊗ₜ u.val.app V x) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp _ _
    (𝟙 F) u V ω x
  have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).map (𝟙 F)).app P =
      𝟙 _ :=
    NatTrans.congr_app
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).map_id _) _
  rwa [hid, Category.id_comp] at h

/-- **The wedge map kills the relation of [Stacks, Tag 01CJ]**, on a nested pure tensor. -/
theorem wedgeHom_tensorLeftMap_relComplex_f_unit
    (r' : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (k : ℕ) (V : (Opens ↥X)ᵒᵖ) (ω : (A'.exteriorPower r').val.obj V) (a : E'.val.obj V)
    (b : (A.exteriorPower k).val.obj V) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
        (A'.exteriorPower r')).map (relComplex A A'' f g hfg k).f ≫
          wedgeHom A' A f r' (k + 1)).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj E').obj
                (A.exteriorPower
                k))).app V
          (ω ⊗ₜ (PresheafOfModules.tensorSheafUnit E' (A.exteriorPower k)).app V (a ⊗ₜ b))) =
      0 := by
  have hdeg : (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ) := by omega
  have hrel : (relComplex A A'' f g hfg k).f.val.app V
        ((PresheafOfModules.tensorSheafUnit E' (A.exteriorPower k)).app V (a ⊗ₜ b)) =
      Stacks.degCast (F := fun l : ℤ => ((A.exterior.piece l).val.obj V : Type u)) hdeg
        ((A.exterior.mul 1 (k : ℤ)).app V
          (A.exteriorGenerator.val.app V (f.val.app V a)) b) :=
    Eq.trans (_root_.SheafOfModules.GradedAlgebra.presentationShortComplex_f_unit
        A.exterior_isExteriorAlgebra.isUniversal f g _ _ (k : ℤ) ((k + 1 : ℕ) : ℤ) hdeg V a b)
      (_root_.SheafOfModules.SymPresentation.eqToHom_val_app A.exterior.piece hdeg V _)
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower r')).map (relComplex A A'' f g hfg k).f)
    (wedgeHom A' A f r' (k + 1)) V _) ?_
  refine Eq.trans (congrArg ((wedgeHom A' A f r' (k + 1)).val.app V)
    (tensorLeftMap_unit (relComplex A A'' f g hfg k).f V ω _)) ?_
  refine Eq.trans (wedgeHom_unit A' A f r' (k + 1) V ω _) ?_
  refine Eq.trans (congrArg
    (fun y => (A.exterior.mul (r' : ℤ) ((k + 1 : ℕ) : ℤ)).app V
      (((extHom A' A f).app (r' : ℤ)).val.app V ω) y)
    hrel) ?_
  refine (A.exterior.toPresheafGradedAlgebra).incl_inj_of_proj
    (i := (r' : ℤ) + ((k + 1 : ℕ) : ℤ)) ?_
  refine Eq.trans ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl (r' : ℤ)
    ((k + 1 : ℕ) : ℤ) _ _).symm ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl (r' : ℤ)
    (((extHom A' A f).app (r' : ℤ)).val.app V ω) * z)
    ((A.exterior.toPresheafGradedAlgebra).incl_degCast hdeg _)) ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl (r' : ℤ)
    (((extHom A' A f).app (r' : ℤ)).val.app V ω) * z)
    ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl 1 (k : ℤ)
      (A.exteriorGenerator.val.app V (f.val.app V a)) b).symm) ?_
  refine Eq.trans (mul_assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z * (A.exterior.toPresheafGradedAlgebra).incl (k : ℤ) b)
    ((A.exterior.toPresheafGradedAlgebra).incl_mul_incl (r' : ℤ) 1 _ _)) ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.toPresheafGradedAlgebra).incl ((r' : ℤ) + 1) z *
    (A.exterior.toPresheafGradedAlgebra).incl (k : ℤ) b)
    (mul_extHom_generator_eq_zero A' A f r' V ω a)) ?_
  rw [(A.exterior.toPresheafGradedAlgebra).incl_zero, zero_mul,
    (A.exterior.toPresheafGradedAlgebra).incl_zero]

/-- **The wedge map kills the relation of [Stacks, Tag 01CJ].** This is what makes the wedge
map descend along the presentation of `⋀ʳ'' E''` by `⋀ʳ'' E`. -/
theorem wedgeHom_tensorLeftMap_relComplex_f
    (r' : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (k : ℕ) :
    (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
          (A'.exteriorPower r')).map (relComplex A A'' f g hfg k).f ≫
        wedgeHom A' A f r' (k + 1) = 0 :=
  tensorSheaf_hom_ext_right (F := A'.exteriorPower r') (G := E') (H := A.exteriorPower k)
    (Q := A.exteriorPower (r' + (k + 1)))
    (φ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower r')).map (relComplex A A'' f g hfg k).f ≫
        wedgeHom A' A f r' (k + 1))
    (ψ := (0 : (show _root_.SheafOfModules.{u}
            (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
          (A'.exteriorPower r')).obj (relComplex A A'' f g hfg k).X₁ ⟶
      A.exteriorPower (r' + (k + 1))))
    fun V w a b =>
      (wedgeHom_tensorLeftMap_relComplex_f_unit A' A A'' f g hfg r' k V w a b).trans rfl

end Vanishing

/-! ### The canonical determinant comparison -/

section Descent

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The category of sheaves of modules is balanced, being abelian. -/
theorem balanced_sheafOfModules :
    CategoryTheory.Balanced (_root_.SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  ⟨fun fm _ _ => (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap fm).2 fun x =>
    ⟨(AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap fm).1 inferInstance x,
      (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap fm).1 inferInstance x⟩⟩

/-- The exactness of the tensored presentation, as a colimit: `⋀ʳ' E' ⊗ ⋀ᵏ⁺¹ E''` is the
cokernel of `⋀ʳ' E' ⊗ (E' ⊗ ⋀ᵏ E) ⟶ ⋀ʳ' E' ⊗ ⋀ᵏ⁺¹ E`, because the sequence of
[Stacks, Tag 01CJ] is a presentation and the tensor product is right exact. -/
noncomputable def relCokernelIsColimit
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (r' k : ℕ) :
    Limits.IsColimit (@Limits.CokernelCofork.map _ _ _ _ _ _ _ _ _
      (Limits.CokernelCofork.ofπ (relComplex A A'' f g hfg k).g
        (relComplex A A'' f g hfg k).zero)
      (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
            _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
            (A'.exteriorPower r'))
      (Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r'))) := by
  letI : (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
        _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
        (A'.exteriorPower r')).PreservesZeroMorphisms :=
    Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
      (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r')
  letI : ∀ {P Q : _root_.SheafOfModules.{u}
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (h h' : P ⟶ Q),
      Limits.PreservesColimit (Limits.parallelPair h h')
        (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
              _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
              (A'.exteriorPower r')) := fun h h' =>
    Stacks.SheafOfModules.TensorLocalProperties.preservesColimit_parallelPair_tensorSheafRight
      (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r') h h'
  have hepi : Epi (relComplex A A'' f g hfg k).g :=
    (_root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact A.exteriorGenerator
      A''.exteriorGenerator A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g f hfg
      hS k).2
  have hbal := balanced_sheafOfModules (X := X) (Osharp := Osharp)
  exact Limits.CokernelCofork.mapIsColimit _
    (_root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact A.exteriorGenerator
      A''.exteriorGenerator A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g f hfg
      hS k).1.gIsCokernel
        (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
              _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
              (A'.exteriorPower r'))

/-- **The canonical comparison `⋀ʳ' E' ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ʳ'⁺ᵏ⁺¹ E`** attached to a short exact
sequence `0 → E' → E → E'' → 0` of sheaves of modules with `E'` finite locally free of rank
`r'`.

It is the descent of the wedge map `⋀ʳ' E' ⊗ ⋀ᵏ⁺¹ E ⟶ ⋀ʳ'⁺ᵏ⁺¹ E` along the presentation
`E' ⊗ ⋀ᵏ E ⟶ ⋀ᵏ⁺¹ E ⟶ ⋀ᵏ⁺¹ E'' ⟶ 0` of [Stacks, Tag 01CJ] tensored with `⋀ʳ' E'`, which is
still a presentation because the tensor product of sheaves of modules is right exact. -/
noncomputable def detComparison
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r'] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower
        r')).obj
        (A''.exteriorPower (k + 1)) ⟶
      A.exteriorPower (r' + (k + 1)) :=
  (relCokernelIsColimit A' A A'' f g hfg hS r' k).desc
    (Limits.CokernelCofork.ofπ (wedgeHom A' A f r' (k + 1))
      (wedgeHom_tensorLeftMap_relComplex_f A' A A'' f g hfg r' k))

/-- **The defining equation of the canonical comparison**: precomposed with `⋀ʳ' E'` tensored
with the degree-`k+1` exterior power of `g`, it is the wedge map. That morphism is an
epimorphism, so this equation determines `detComparison`. -/
theorem tensorLeftMap_comp_detComparison
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r'] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower r')).map ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)) ≫
        detComparison A' A A'' f g hfg hS r' k =
      wedgeHom A' A f r' (k + 1) :=
  Limits.Cofork.IsColimit.π_desc (relCokernelIsColimit A' A A'' f g hfg hS r' k)

/-- The wedge `t₀ ∧ ⋯ ∧ t_{n-1}` of `n` local sections of a sheaf of modules, as a local
section of the degree-`n` exterior power. -/
noncomputable abbrev wedgeSec
    {M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) M)
    (V : (Opens ↥X)ᵒᵖ) (n : ℕ) (t : Fin n → M.val.obj V) : (B.exteriorPower n).val.obj V :=
  wedgeProd B.exterior V n fun i => B.exteriorGenerator.val.app V (t i)

/-- A homomorphism of exterior algebras carries a wedge of local sections to the wedge of their
images. -/
theorem extHom_wedgeSec
    {M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) M)
    (D : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) N)
    (h : M ⟶ N) (V : (Opens ↥X)ᵒᵖ) (n : ℕ) (t : Fin n → M.val.obj V) :
    ((extHom B D h).app (n : ℤ)).val.app V (wedgeSec B V n t) =
      wedgeSec D V n fun i => h.val.app V (t i) :=
  (unitalHom_homogeneousProd (extHom B D h) V n _).trans
    (congrArg (wedgeProd D.exterior V n) (funext fun i => extHom_app_one B D h V (t i)))

/-- Postcomposing a family with a function commutes with concatenation. -/
theorem fin_append_comp {α β : Type*} (h : α → β) {m n : ℕ} (z : Fin m → α) (w : Fin n → α) :
    (fun i => h (Fin.append z w i)) = Fin.append (fun i => h (z i)) fun i => h (w i) :=
  comp_fin_append h z w

section Equations

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
  (hS : (ShortComplex.mk f g hfg).Exact) (r' k : ℕ)

/-- **The defining equation of the canonical comparison, on local sections.** On the image of
`ω ⊗ ⋀ᵏ⁺¹(g)(η)` the comparison is the wedge of the image of `ω` in `⋀ʳ' E` with `η`. Since
`⋀ᵏ⁺¹(g)` is locally surjective, this is the wedge-and-lift formula of [Stacks, Tag 0B38]: the
value on a tensor of determinant sections is the wedge of the first with **any** local lift of
the second. -/
theorem detComparison_unit [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (V : (Opens ↥X)ᵒᵖ) (ω : (A'.exteriorPower r').val.obj V)
    (η : (A.exteriorPower (k + 1)).val.obj V) :
    (detComparison A' A A'' f g hfg hS r' k).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
            (A''.exteriorPower (k + 1))).app V
          (ω ⊗ₜ ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)).val.app V η)) =
      (A.exterior.mul (r' : ℤ) ((k + 1 : ℕ) : ℤ)).app V
        (((extHom A' A f).app (r' : ℤ)).val.app V ω) η := by
  have h := congrArg (fun m : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower r')).obj (A.exteriorPower (k + 1)) ⟶ A.exteriorPower (r' + (k + 1)) =>
      m.val.app V ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
        (A.exteriorPower (k + 1))).app V (ω ⊗ₜ η)))
    (tensorLeftMap_comp_detComparison A' A A'' f g hfg hS r' k)
  refine Eq.trans ?_ (h.trans (wedgeHom_unit A' A f r' (k + 1) V ω η))
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ V _).symm
  exact congrArg ((detComparison A' A A'' f g hfg hS r' k).val.app V)
    (tensorLeftMap_unit ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)) V ω η).symm

/-- **Stacks 0B38, the wedge-and-lift formula.** The canonical comparison carries the image of
`(s₁ ∧ ⋯ ∧ s_{r'}) ⊗ (g(l₁) ∧ ⋯ ∧ g(l_{k+1}))` to
`f(s₁) ∧ ⋯ ∧ f(s_{r'}) ∧ l₁ ∧ ⋯ ∧ l_{k+1}`: the wedge of the images of the sections of `E'` with
**arbitrary local lifts** `lⱼ` of the sections of `E''`. This equation is the one the source
gives for its canonical map, and it determines the comparison, since the wedges of local
sections generate the exterior powers locally.

Here `det` is the top exterior power, which
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower` identifies with the
`det` of [Stacks, Tag 0FJN] at constant rank; what is carried here is `E'` of constant rank `r'`
and `E''` of constant rank `r'' = k + 1`. The ISOMORPHISM clause of the tag is carried separately
by `Stacks.SheafOfModules.TopWedge.isIso_detComparison`.

This is the CONSTANT-RANK form of the tag. The general case — a short exact sequence of finite
locally free sheaves with no constant-rank hypothesis — is carried by
`Stacks.SheafOfModules.TopWedge.detSummandComparison_ι_unit_wedge` and
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`. -/
@[stacks 0B38 "the CONSTANT-RANK form of the canonical map det(E')⊗det(E'')⟶det(E) and of its \
wedge-and-lift formula"]
theorem detComparison_wedge [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (V : (Opens ↥X)ᵒᵖ) (s : Fin r' → E'.val.obj V) (l : Fin (k + 1) → E.val.obj V) :
    (detComparison A' A A'' f g hfg hS r' k).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
            (A''.exteriorPower (k + 1))).app V
          (wedgeSec A' V r' s ⊗ₜ wedgeSec A'' V (k + 1) fun i => g.val.app V (l i))) =
      wedgeSec A V (r' + (k + 1)) (Fin.append (fun i => f.val.app V (s i)) l) := by
  refine Eq.trans (congrArg (fun y => (detComparison A' A A'' f g hfg hS r' k).val.app V
      ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
        (A''.exteriorPower (k + 1))).app V (wedgeSec A' V r' s ⊗ₜ y)))
    (extHom_wedgeSec A A'' g V (k + 1) l).symm) ?_
  refine Eq.trans (detComparison_unit A' A A'' f g hfg hS r' k V _ (wedgeSec A V (k + 1) l)) ?_
  refine Eq.trans (congrArg (fun z => (A.exterior.mul (r' : ℤ) ((k + 1 : ℕ) : ℤ)).app V z
      (wedgeSec A V (k + 1) l)) (extHom_wedgeSec A' A f V r' s)) ?_
  refine Eq.trans (homogeneousProd_append A.exterior.toPresheafGradedAlgebra V r' (k + 1) _ _) ?_
  exact congrArg (wedgeProd A.exterior V (r' + (k + 1)))
    (fin_append_comp (A.exteriorGenerator.val.app V) (fun i => f.val.app V (s i)) l).symm

/-- **The canonical comparison is the only morphism satisfying its defining equation.** The
morphism `⋀ʳ' E' ⊗ ⋀ᵏ⁺¹(g)` is an epimorphism, so a morphism out of `⋀ʳ' E' ⊗ ⋀ᵏ⁺¹ E''` is
determined by its composite with it. -/
@[stacks 0B38 "uniqueness of the map satisfying the wedge-and-lift formula, which is the \
precise sense of CANONICAL here — again in the constant-rank form, with the same carried \
hypotheses as `detComparison_wedge`; the isomorphism clause is carried by \
`Stacks.SheafOfModules.TopWedge.isIso_detComparison`, and the general case by \
`Stacks.SheafOfModules.TopWedge.eq_determinantTensorDeterminantHom`"]
theorem eq_detComparison [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower
        r')).obj
        (A''.exteriorPower (k + 1)) ⟶
      A.exteriorPower (r' + (k + 1)))
    (hψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower r')).map ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)) ≫ ψ =
      wedgeHom A' A f r' (k + 1)) :
    ψ = detComparison A' A A'' f g hfg hS r' k := by
  have hepi' : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
    (A'.exteriorPower r')).map ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ))) :=
    Limits.epi_of_isColimit_cofork (relCokernelIsColimit A' A A'' f g hfg hS r' k)
  exact (cancel_epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
    (A'.exteriorPower r')).map ((extHom A A'' g).app ((k + 1 : ℕ) : ℤ)))).1
    (hψ.trans (tensorLeftMap_comp_detComparison A' A A'' f g hfg hS r' k).symm)

end Equations

end Descent

end Stacks.SheafOfModules.TopWedge

end
