module

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCohomologyBridge
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickening
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The edge map from the cohomology of a direct image

Let `p : X ⟶ Y` be a morphism of schemes, `π : Y ⟶ Spec R` a structure morphism and `G` an
`𝒪_X`-module. The Leray spectral sequence of `p` has an edge map `Hⁿ(Y, p_* G) ⟶ Hⁿ(X, G)`. This
file constructs it, with values in abelian groups and for every `𝒪_X`-module `G`, as a natural
transformation

`edgeMap p π n : p_* ⋙ |Hⁿ_π(Y, -)| ⟶ |Hⁿ_{p ≫ π}(X, -)|`,

and proves the four properties for which it is used:

* in degree zero it is the identity `Γ(Y, p_* G) = Γ(X, G)`;
* it commutes with the connecting morphisms of every short exact sequence `S` of `𝒪_X`-modules
  whose direct image `p_* S` is again short exact;
* it is an isomorphism at `G` as soon as the higher direct images `R^q p_* G` vanish for `q > 0`
  (Stacks 01F4, part (1)), in particular when `p` is affine and `G` is quasi-coherent
  (Stacks 01XC);
* on such `G` it is the only family of maps with the first two properties.

The construction uses universality only. `|Hⁿ_π(Y, -)|` is a universal δ-functor on
`𝒪_Y`-modules (Stacks 010T), so the pullback of global sections `Γ(Y, F) ⟶ Γ(X, p⁻¹ F_ab)` along
the continuous map underlying `p` extends uniquely to a morphism of δ-functors `pullbackHom`
from it to `F ↦ H'ⁿ(X, p⁻¹ F_ab)`, the cohomology of the abelian inverse image, which is exact
with no hypothesis on `p`. Evaluating at `p_* G`, applying `H'ⁿ` of the counit
`p⁻¹ (p_* G)_ab ⟶ G_ab` of the abelian adjunction and then the inverse of the comparison
`|Hⁿ(X, G)| ≅ H'ⁿ(X, G_ab)` of Stacks 03FD gives the edge map. Each of the three pieces commutes
with connecting morphisms wherever it is defined, and the counit does so on sequences that
`p_*` keeps exact; this is all `edgeMap_δ` uses. Invertibility is the dimension shift of
Stacks 01F4: an injective `𝒪_X`-module `I` has `p_* I` acyclic for global sections (Stacks 01EX,
part (2)), and the cokernel of `G ⟶ I` again has vanishing higher direct images.

The same uniqueness compares the edge maps of `p` and of a composite `i ≫ p` with an exact
direct image `i_*`, for instance a closed immersion: through `p'_* G ≅ p_* i_* G` the edge map of
`p' = i ≫ p` at `G` is the edge map of `p` at `i_* G` followed by the comparison
`|Hⁿ(X, i_* G)| ≅ |Hⁿ(X', G)|` of `thickeningIso`. This is the form in which the edge map enters
the obstruction theory of Stacks 07YH, for the base-change immersion `W_{T'} ⟶ W_T` over `W`.

## Main definitions

* `CategoryTheory.DeltaFunctor.edgeHom`: the composite `P ⋙ Dⁿ ⟶ Eⁿ` of a morphism of
  δ-functors `D ⟶ H ∘ Ψ₁`, a natural transformation `P ⋙ Ψ₁ ⟶ Ψ₂` and a morphism of δ-functors
  `H ∘ Ψ₂ ⟶ E`, for exact `Ψ₁`, `Ψ₂`.
* `CategoryTheory.DeltaFunctor.compAlong`: the composite of families `P ⋙ Dⁿ ⟶ Eⁿ` and
  `Q ⋙ Eⁿ ⟶ Fⁿ` along an isomorphism `R ≅ Q ⋙ P`.
* `Deformation.Artin.SectionsSheaf.pullbackHom`: the pullback of cohomology along `p`, as a
  morphism of δ-functors `|Hⁿ_π(Y, F)| ⟶ H'ⁿ(X, p⁻¹ F_ab)`.
* `Deformation.Artin.SectionsSheaf.pushforwardCounit`: the counit `p⁻¹ (p_* G)_ab ⟶ G_ab`.
* `Deformation.Artin.SectionsSheaf.edgeMap`: the edge map, and `edgeIso`, the isomorphism it is
  for `p` affine and `G` quasi-coherent.
* `Deformation.Artin.SectionsSheaf.edgeDeltaHom`: for an exact direct image, the edge map as a
  morphism of δ-functors.

## Main results

* `CategoryTheory.DeltaFunctor.isIso_app_of_comp_δ` and
  `CategoryTheory.DeltaFunctor.app_eq_of_comp_δ`: the dimension shift, for a family of maps
  `P ⋙ Dⁿ ⟶ Eⁿ` commuting with connecting morphisms on the sequences that `P` keeps exact.
* `Deformation.Artin.SectionsSheaf.edgeMap_zero`, `abCohomologyZeroIso_inv_app_comp_edgeMap_app`:
  in degree zero the edge map is the identity on global sections.
* `Deformation.Artin.SectionsSheaf.edgeMap_δ`: the edge map commutes with the connecting
  morphisms.
* `Deformation.Artin.SectionsSheaf.isIso_edgeMap_app` (Stacks 01F4, part (1)) and
  `isIso_edgeMap_app_of_isQuasicoherent`: the edge map is an isomorphism when the higher direct
  images vanish.
* `Deformation.Artin.SectionsSheaf.app_eq_edgeMap_app`: uniqueness of the edge map.
* `Deformation.Artin.SectionsSheaf.edgeDeltaHom_eq_thickeningIso`: for an exact direct image the
  edge map is `thickeningIso`.
* `Deformation.Artin.SectionsSheaf.edgeMap_app_eq_of_comp_eq`, `edgeMap_comp_closedImmersion`
  and `edgeMap_app_pullback_snd`: the edge map of `i ≫ p` through the edge map of `p` and
  `thickeningIso`, for `i_*` exact.

## Implementation notes

The edge map is not built from `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso`
(Stacks 089W), which is the same isomorphism on quasi-coherent modules for `p` affine but carries
no information about connecting morphisms.

The general statements `compAlong`, `isIso_app_of_comp_δ` and `app_eq_of_comp_δ` are stated
over preadditive source categories. The δ-functor `abCohomology` carries the preadditive
structure of `SheafOfModules` found directly by instance search; stated over abelian sources
these lemmas ask the elaborator to solve `Abelian.toPreadditive ?_` against it while the
instance is still a metavariable, and applying them exhausts the heartbeat
budget. `edgeHom` needs abelian sources, because `CategoryTheory.DeltaFunctor.precomp` does; it
is only ever applied with the morphisms of δ-functors given first, which fixes those instances.

The edge map is assembled by `edgeHom` in a general context so that the definitional unfolding
of `CategoryTheory.DeltaFunctor.precomp` it relies on is checked once, on variables. Defining the
counit in cohomology directly as a map out of `p_* ⋙ (H'deltaFunctor ⊤).precomp Ψ` instead costs
about a minute of kernel time, the kernel comparing `p_* ⋙ Ψ ⋙ H'ⁿ` with
`(p_* ⋙ Ψ) ⋙ H'ⁿ` by unfolding the direct image. The specializations still cost kernel time:
`edgeMap_app`, `edgeMap_δ` and `edgeMap_app_zero` take 13 to 28 s each, every other declaration
under 6 s, and the whole file about two minutes.

## References

* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ u


namespace CategoryTheory.DeltaFunctor

section Aux

variable {C : Type u₁} [Category.{v₁} C]

private theorem comp₃_comp_eq {A₃ B₃ C₃ D₃ A₁ B₁ C₁ D₁ : C}
    {a₃ : A₃ ⟶ B₃} {b₃ : B₃ ⟶ C₃} {c₃ : C₃ ⟶ D₃} {a₁ : A₁ ⟶ B₁} {b₁ : B₁ ⟶ C₁}
    {c₁ : C₁ ⟶ D₁} {dA : A₃ ⟶ A₁} {dB : B₃ ⟶ B₁} {dC : C₃ ⟶ C₁} {dD : D₃ ⟶ D₁}
    (h₁ : a₃ ≫ dB = dA ≫ a₁) (h₂ : b₃ ≫ dC = dB ≫ b₁) (h₃ : c₃ ≫ dD = dC ≫ c₁) :
    (a₃ ≫ b₃ ≫ c₃) ≫ dD = dA ≫ a₁ ≫ b₁ ≫ c₁ := by
  rw [Category.assoc, Category.assoc, h₃, reassoc_of% h₂, reassoc_of% h₁]

private theorem comp_zero_eq {A B B' D E F G : C} {z : A ⟶ B} {s : B ⟶ B'} {i : B' ⟶ D}
    {m : D ⟶ E} {h : E ⟶ F} {z' : F ⟶ G} {r : B' ⟶ F} {q : B ⟶ F}
    (hr : i ≫ m ≫ h = r) (hq : s ≫ r = q) :
    (z ≫ s ≫ i) ≫ m ≫ h ≫ z' = z ≫ q ≫ z' := by
  rw [← hq, ← hr]
  simp only [Category.assoc]

private theorem comp₄_eq {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C} {a : X₀ ⟶ Y₀} {b : Y₀ ⟶ Y₁}
    {c : Y₁ ⟶ Y₂} {d : Y₂ ⟶ Y₃} {u : X₀ ⟶ X₁} {v : X₁ ⟶ Y₁} {w : X₁ ⟶ X₂} {x : X₂ ⟶ Y₂}
    {y : X₂ ⟶ X₃} {t : X₃ ⟶ Y₃} {r : X₀ ⟶ X₃} (h₁ : a ≫ b = u ≫ v) (h₂ : v ≫ c = w ≫ x)
    (h₃ : x ≫ d = y ≫ t) (h₄ : u ≫ w ≫ y = r) : a ≫ b ≫ c ≫ d = r ≫ t := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, ← h₄]
  simp only [Category.assoc]

private theorem id_comp_id_comp_eq {B D : C} {x a : B ⟶ B} {c c' : B ⟶ D} (hx : x = 𝟙 B)
    (ha : a = 𝟙 B) (hc : c = c') : x ≫ a ≫ c = c' := by
  rw [hx, ha, Category.id_comp, Category.id_comp, hc]

private theorem comp_comp_comp_eq {A B B' B'' D : C} {u : A ⟶ B} {r : B ⟶ B'}
    {a : B' ⟶ B''} {c : B'' ⟶ D} {c' : B ⟶ D} {e : A ⟶ D} (hr : r ≫ a ≫ c = c')
    (hk : u ≫ c' = e) : ((u ≫ r) ≫ a) ≫ c = e := by
  rw [Category.assoc, Category.assoc, hr, hk]

end Aux

/-! ### Connecting morphisms of precomposed δ-functors -/

section Precomp

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {A₁ : Type u₂} [Category.{v₂} A₁] [Abelian A₁]
  {A₂ : Type u₃} [Category.{v₃} A₂] [Abelian A₂]
  {C : Type u₄} [Category.{v₄} C] [Abelian C]
  (H : DeltaFunctor A C)
  {Ψ₁ : A₁ ⥤ A} [Ψ₁.Additive] [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁]
  {Ψ₂ : A₂ ⥤ A} [Ψ₂.Additive] [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂]
  {P : A₂ ⥤ A₁} [P.PreservesZeroMorphisms]

/-- **The connecting morphisms of two precomposites of a δ-functor are natural along a
transformation of the precomposing functors.** For exact functors `Ψ₁ : A₁ ⥤ A` and
`Ψ₂ : A₂ ⥤ A`, a functor `P : A₂ ⥤ A₁` and a natural transformation `τ : P ⋙ Ψ₁ ⟶ Ψ₂`, the
squares `Hⁿ(τ_{S.X₃}) ≫ δ = δ ≫ Hⁿ⁺¹(τ_{S.X₁})` commute for every short exact sequence `S` of
`A₂` whose image under `P` is short exact; `P` itself need not be exact. -/
@[reassoc]
theorem precomp_δ_naturality (τ : P ⋙ Ψ₁ ⟶ Ψ₂) {S : ShortComplex A₂} (hS : S.ShortExact)
    (hPS : (S.map P).ShortExact) (n : ℕ) :
    (H.functor n).map (τ.app S.X₃) ≫ (H.precomp Ψ₂).δ hS n =
      (H.precomp Ψ₁).δ hPS n ≫ (H.functor (n + 1)).map (τ.app S.X₁) :=
  H.δ_naturality (hPS.map_of_exact Ψ₁) (hS.map_of_exact Ψ₂)
    { τ₁ := τ.app S.X₁
      τ₂ := τ.app S.X₂
      τ₃ := τ.app S.X₃
      comm₁₂ := (τ.naturality S.f).symm
      comm₂₃ := (τ.naturality S.g).symm } n

end Precomp

/-! ### Edge morphisms -/

section Edge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {A₁ : Type u₂} [Category.{v₂} A₁] [Abelian A₁]
  {A₂ : Type u₃} [Category.{v₃} A₂] [Abelian A₂]
  {C : Type u₄} [Category.{v₄} C] [Abelian C]
  {H : DeltaFunctor A C}
  {Ψ₁ : A₁ ⥤ A} [Ψ₁.Additive] [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁]
  {Ψ₂ : A₂ ⥤ A} [Ψ₂.Additive] [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂]
  {P : A₂ ⥤ A₁} {D : DeltaFunctor A₁ C} {E : DeltaFunctor A₂ C}

/-- **The edge morphism through a δ-functor precomposed with two exact functors.** For exact
functors `Ψ₁ : A₁ ⥤ A` and `Ψ₂ : A₂ ⥤ A`, a functor `P : A₂ ⥤ A₁` (not assumed exact), morphisms
of δ-functors `α : D ⟶ H ∘ Ψ₁` on `A₁` and `β : H ∘ Ψ₂ ⟶ E` on `A₂`, and a natural transformation
`τ : P ⋙ Ψ₁ ⟶ Ψ₂`, the composite `P ⋙ Dⁿ ⟶ P ⋙ Ψ₁ ⋙ Hⁿ ⟶ Ψ₂ ⋙ Hⁿ ⟶ Eⁿ`. The Leray edge map
`Hⁿ(Y, p_* G) ⟶ Hⁿ(X, G)` has this shape, with `P` the direct image. -/
def edgeHom (α : D ⟶ H.precomp Ψ₁) (τ : P ⋙ Ψ₁ ⟶ Ψ₂) (β : H.precomp Ψ₂ ⟶ E) (n : ℕ) :
    P ⋙ D.functor n ⟶ E.functor n :=
  Functor.whiskerLeft P (α.app n) ≫ Functor.whiskerRight τ (H.functor n) ≫ β.app n

variable (α : D ⟶ H.precomp Ψ₁) (τ : P ⋙ Ψ₁ ⟶ Ψ₂) (β : H.precomp Ψ₂ ⟶ E)

/-- The components of `edgeHom`. -/
theorem edgeHom_app (n : ℕ) (G : A₂) :
    (edgeHom α τ β n).app G =
      (α.app n).app (P.obj G) ≫ (H.functor n).map (τ.app G) ≫ (β.app n).app G :=
  rfl

/-- **The edge morphism in degree zero.** If, in degree zero, `α` is a map `σ : Γ ⟶ Ψ₁ ⋙ K`
read through identifications `D⁰ ≅ Γ` and `H⁰ ≅ K`, `β` is the identity read through `H⁰ ≅ K`
and `E⁰ ≅ Ψ₂ ⋙ K`, and `σ` followed by `K(τ)` is `θ : P ⋙ Γ ⟶ Ψ₂ ⋙ K`, then the edge morphism
in degree zero is `θ`, read through `D⁰ ≅ Γ` and `E⁰ ≅ Ψ₂ ⋙ K`. -/
theorem edgeHom_app_zero {Γ : A₁ ⥤ C} {K : A ⥤ C} (e₁ : D.functor 0 ≅ Γ)
    (e₂ : E.functor 0 ≅ Ψ₂ ⋙ K) (ι : H.functor 0 ≅ K) (σ : Γ ⟶ Ψ₁ ⋙ K)
    (θ : P ⋙ Γ ⟶ Ψ₂ ⋙ K) (hα : α.app 0 = e₁.hom ≫ σ ≫ Functor.whiskerLeft Ψ₁ ι.inv)
    (hβ : β.app 0 = Functor.whiskerLeft Ψ₂ ι.hom ≫ e₂.inv)
    (hσ : ∀ G : A₂, σ.app (P.obj G) ≫ K.map (τ.app G) = θ.app G) (G : A₂) :
    (edgeHom α τ β 0).app G = e₁.hom.app (P.obj G) ≫ θ.app G ≫ e₂.inv.app G := by
  rw [edgeHom_app, hα, hβ]
  exact comp_zero_eq (NatIso.naturality_1 ι (τ.app G)) (hσ G)

variable [P.PreservesZeroMorphisms]

/-- **The edge morphism commutes with the connecting morphisms** of every short exact sequence
`S` of `A₂` whose image under `P` is short exact. -/
theorem edgeHom_comp_δ {S : ShortComplex A₂} (hS : S.ShortExact)
    (hPS : (S.map P).ShortExact) (n : ℕ) :
    (edgeHom α τ β n).app S.X₃ ≫ E.δ hS n = D.δ hPS n ≫ (edgeHom α τ β (n + 1)).app S.X₁ := by
  rw [edgeHom_app, edgeHom_app]
  exact comp₃_comp_eq (α.comm hPS n) (precomp_δ_naturality H τ hS hPS n) (β.comm hS n)

end Edge

/-! ### Composing families compatible with connecting morphisms -/

section Comp

variable {A₀ : Type u₁} [Category.{v₁} A₀] [Preadditive A₀]
  {A₁ : Type u₂} [Category.{v₂} A₁] [Preadditive A₁]
  {A₂ : Type u₃} [Category.{v₃} A₂] [Preadditive A₂]
  {C : Type u₄} [Category.{v₄} C] [Preadditive C]
  {D : DeltaFunctor A₀ C} {E : DeltaFunctor A₁ C} {F : DeltaFunctor A₂ C}
  {P : A₁ ⥤ A₀} {Q : A₂ ⥤ A₁} {R : A₂ ⥤ A₀}

/-- **The composite of two edge families along `R ≅ Q ⋙ P`.** For families
`ε n : P ⋙ Dⁿ ⟶ Eⁿ` and `κ n : Q ⋙ Eⁿ ⟶ Fⁿ`, the family `R ⋙ Dⁿ ⟶ (Q ⋙ P) ⋙ Dⁿ ⟶ Q ⋙ Eⁿ ⟶ Fⁿ`.
For direct images along `X' ⟶ X ⟶ Y` this composes the edge map of `X ⟶ Y` with that of
`X' ⟶ X`. -/
def compAlong (e : R ≅ Q ⋙ P) (ε : ∀ n, P ⋙ D.functor n ⟶ E.functor n)
    (κ : ∀ n, Q ⋙ E.functor n ⟶ F.functor n) (n : ℕ) : R ⋙ D.functor n ⟶ F.functor n :=
  Functor.whiskerRight e.hom (D.functor n) ≫ (Functor.associator Q P (D.functor n)).hom ≫
    Functor.whiskerLeft Q (ε n) ≫ κ n

variable (e : R ≅ Q ⋙ P) (ε : ∀ n, P ⋙ D.functor n ⟶ E.functor n)
  (κ : ∀ n, Q ⋙ E.functor n ⟶ F.functor n)

/-- The components of `compAlong`. -/
theorem compAlong_app (n : ℕ) (G : A₂) :
    (compAlong e ε κ n).app G =
      (D.functor n).map (e.hom.app G) ≫ (ε n).app (Q.obj G) ≫ (κ n).app G := by
  simp [compAlong]

/-- **`compAlong` in degree zero**: if `ε 0` and `κ 0` are maps `θP` and `θQ` read through
identifications of the degree-zero parts with functors `Γᵢ`, and `Γ₀(e)` followed by `θP` and
`θQ` is `θR`, then `compAlong e ε κ 0` is `θR` read through the same identifications. -/
theorem compAlong_app_zero {Γ₀ : A₀ ⥤ C} {Γ₁ : A₁ ⥤ C} {Γ₂ : A₂ ⥤ C}
    (z₀ : D.functor 0 ≅ Γ₀) (z₁ : E.functor 0 ≅ Γ₁) (z₂ : F.functor 0 ≅ Γ₂)
    (θP : P ⋙ Γ₀ ⟶ Γ₁) (θQ : Q ⋙ Γ₁ ⟶ Γ₂) (θR : R ⋙ Γ₀ ⟶ Γ₂)
    (hε : ∀ G, z₀.inv.app (P.obj G) ≫ (ε 0).app G = θP.app G ≫ z₁.inv.app G)
    (hκ : ∀ G, z₁.inv.app (Q.obj G) ≫ (κ 0).app G = θQ.app G ≫ z₂.inv.app G)
    (hθ : ∀ G, Γ₀.map (e.hom.app G) ≫ θP.app (Q.obj G) ≫ θQ.app G = θR.app G) (G : A₂) :
    z₀.inv.app (R.obj G) ≫ (compAlong e ε κ 0).app G = θR.app G ≫ z₂.inv.app G := by
  rw [compAlong_app]
  exact comp₄_eq (z₀.inv.naturality (e.hom.app G)).symm (hε (Q.obj G)) (hκ G) (hθ G)

variable [P.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]

/-- **`compAlong` commutes with the connecting morphisms** of every short exact sequence `S`
of `A₂` whose image under `R` is short exact, provided `Q` preserves short exact sequences, `ε`
commutes with them on sequences that `P` keeps exact and `κ` on sequences that `Q` keeps
exact. -/
theorem compAlong_comp_δ
    (hε : ∀ {S : ShortComplex A₁} (hS : S.ShortExact) (hPS : (S.map P).ShortExact) (n : ℕ),
      (ε n).app S.X₃ ≫ E.δ hS n = D.δ hPS n ≫ (ε (n + 1)).app S.X₁)
    (hκ : ∀ {S : ShortComplex A₂} (hS : S.ShortExact) (hQS : (S.map Q).ShortExact) (n : ℕ),
      (κ n).app S.X₃ ≫ F.δ hS n = E.δ hQS n ≫ (κ (n + 1)).app S.X₁)
    (hQ : ∀ {S : ShortComplex A₂}, S.ShortExact → (S.map Q).ShortExact)
    {S : ShortComplex A₂} (hS : S.ShortExact) (hRS : (S.map R).ShortExact) (n : ℕ) :
    (compAlong e ε κ n).app S.X₃ ≫ F.δ hS n =
      D.δ hRS n ≫ (compAlong e ε κ (n + 1)).app S.X₁ := by
  let φ : S.map R ≅ (S.map Q).map P :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (e.hom.naturality S.f).symm (e.hom.naturality S.g).symm
  have hQS := hQ hS
  have hPQS : ((S.map Q).map P).ShortExact := ShortComplex.shortExact_of_iso φ hRS
  rw [compAlong_app, compAlong_app]
  exact comp₃_comp_eq (D.δ_naturality hRS hPQS φ.hom n) (hε hQS hPQS n) (hκ hS hQS n)

end Comp

/-! ### The dimension shift -/

section DimensionShift

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Preadditive A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Preadditive A₂]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]
  {D : DeltaFunctor A₁ C} {E : DeltaFunctor A₂ C} {P : A₂ ⥤ A₁} [P.PreservesZeroMorphisms]

/-- **The dimension shift.** Let `ε n : P ⋙ Dⁿ ⟶ Eⁿ` be natural transformations commuting with
the connecting morphisms of every short exact sequence that `P` keeps exact. Let `𝒞` be a class
of objects of `A₂` on which `ε 0` is invertible, and such that every object of `𝒞` is the first
term of a short exact sequence `S`, kept exact by `P`, whose other two terms lie in `𝒞` and
whose middle term is killed by `Dⁿ⁺¹ ∘ P` and `Eⁿ⁺¹` in every degree. Then `ε n` is invertible on
`𝒞` in every degree. This is the argument of Stacks 01F4, part (1); the class `𝒞` is that of
the objects with vanishing higher direct images. -/
theorem isIso_app_of_comp_δ (ε : ∀ n, P ⋙ D.functor n ⟶ E.functor n)
    (hε : ∀ {S : ShortComplex A₂} (hS : S.ShortExact) (hPS : (S.map P).ShortExact) (n : ℕ),
      (ε n).app S.X₃ ≫ E.δ hS n = D.δ hPS n ≫ (ε (n + 1)).app S.X₁)
    (𝒞 : ObjectProperty A₂) (h₀ : ∀ G, 𝒞 G → IsIso ((ε 0).app G))
    (heff : ∀ G, 𝒞 G → ∃ (S : ShortComplex A₂) (_ : S.ShortExact)
      (_ : (S.map P).ShortExact), Nonempty (S.X₁ ≅ G) ∧ 𝒞 S.X₂ ∧ 𝒞 S.X₃ ∧
      (∀ n, IsZero ((D.functor (n + 1)).obj (P.obj S.X₂))) ∧
      ∀ n, IsZero ((E.functor (n + 1)).obj S.X₂))
    (n : ℕ) (G : A₂) (hG : 𝒞 G) : IsIso ((ε n).app G) := by
  induction n generalizing G with
  | zero => exact h₀ G hG
  | succ n ih =>
    obtain ⟨S, hS, hPS, ⟨e⟩, h₂, h₃, hDz, hEz⟩ := heff G hG
    have hEpiD : Epi (D.δ hPS n) :=
      D.epi_δ_of_map_f_eq_zero hPS n ((hDz n).eq_of_tgt _ 0)
    have hEpiE : Epi (E.δ hS n) :=
      E.epi_δ_of_map_f_eq_zero hS n ((hEz n).eq_of_tgt _ 0)
    have := ih S.X₂ h₂
    have := ih S.X₃ h₃
    let φ : D.scδ₁ hPS n ⟶ E.scδ₁ hS n :=
      { τ₁ := (ε n).app S.X₂
        τ₂ := (ε n).app S.X₃
        τ₃ := (ε (n + 1)).app S.X₁
        comm₁₂ := ((ε n).naturality S.g).symm
        comm₂₃ := hε hS hPS n }
    have hm : Mono ((ε (n + 1)).app S.X₁) :=
      ShortComplex.mono_of_epi_of_epi_of_mono φ (E.scδ₁_exact hS n) hEpiD
        (inferInstanceAs (Epi ((ε n).app S.X₂))) (inferInstanceAs (Mono ((ε n).app S.X₃)))
    have he : Epi ((ε (n + 1)).app S.X₁) := by
      have : Epi ((ε n).app S.X₃ ≫ E.δ hS n) := epi_comp _ _
      rw [hε hS hPS n] at this
      exact epi_of_epi (D.δ hPS n) _
    have : IsIso ((ε (n + 1)).app S.X₁) := isIso_of_mono_of_epi _
    rw [← NatTrans.naturality_1 (ε (n + 1)) e]
    infer_instance

/-- **Uniqueness by dimension shift.** Two families `P ⋙ Dⁿ ⟶ Eⁿ` commuting with the
connecting morphisms of every short exact sequence that `P` keeps exact, and equal in degree
zero on a class `𝒞`, are equal in every degree on `𝒞`, provided every object of `𝒞` is the first
term of a short exact sequence, kept exact by `P`, whose third term lies in `𝒞` and whose middle
term is killed by `Dⁿ⁺¹ ∘ P` in every degree. -/
theorem app_eq_of_comp_δ (ε ε' : ∀ n, P ⋙ D.functor n ⟶ E.functor n)
    (hε : ∀ {S : ShortComplex A₂} (hS : S.ShortExact) (hPS : (S.map P).ShortExact) (n : ℕ),
      (ε n).app S.X₃ ≫ E.δ hS n = D.δ hPS n ≫ (ε (n + 1)).app S.X₁)
    (hε' : ∀ {S : ShortComplex A₂} (hS : S.ShortExact) (hPS : (S.map P).ShortExact) (n : ℕ),
      (ε' n).app S.X₃ ≫ E.δ hS n = D.δ hPS n ≫ (ε' (n + 1)).app S.X₁)
    (𝒞 : ObjectProperty A₂) (h₀ : ∀ G, 𝒞 G → (ε 0).app G = (ε' 0).app G)
    (heff : ∀ G, 𝒞 G → ∃ (S : ShortComplex A₂) (_ : S.ShortExact)
      (_ : (S.map P).ShortExact), Nonempty (S.X₁ ≅ G) ∧ 𝒞 S.X₃ ∧
      ∀ n, IsZero ((D.functor (n + 1)).obj (P.obj S.X₂)))
    (n : ℕ) (G : A₂) (hG : 𝒞 G) : (ε n).app G = (ε' n).app G := by
  induction n generalizing G with
  | zero => exact h₀ G hG
  | succ n ih =>
    obtain ⟨S, hS, hPS, ⟨e⟩, h₃, hDz⟩ := heff G hG
    have hEpiD : Epi (D.δ hPS n) :=
      D.epi_δ_of_map_f_eq_zero hPS n ((hDz n).eq_of_tgt _ 0)
    have h : (ε (n + 1)).app S.X₁ = (ε' (n + 1)).app S.X₁ := by
      rw [← cancel_epi (D.δ hPS n), ← hε hS hPS n, ← hε' hS hPS n, ih S.X₃ h₃]
    rw [← NatTrans.naturality_1 (ε (n + 1)) e, ← NatTrans.naturality_1 (ε' (n + 1)) e, h]

end DimensionShift

end CategoryTheory.DeltaFunctor

/-! ### Native cohomology in degree zero -/

namespace Stacks.Cohomology.AbelianColimit

variable {Z : Type u} [TopologicalSpace Z]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]

/-- **In degree zero, native cohomology over an open `U` is sections over `U`**, with source
the degree-zero part of `H'deltaFunctor U` on the nose: `Ext⁰` out of the sheaf `freeOfOpen U`
corepresenting sections. This is `Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso`, whose
source `H'functor U 0` agrees with this one only after unfolding `Ext`. -/
def H'deltaFunctorZeroIso (U : TopologicalSpace.Opens Z) :
    (H'deltaFunctor U).functor 0 ≅ abSections U :=
  Functor.leftUnitor _ ≪≫ ModuleSheafCohomology.extZeroIsoCoyoneda (freeOfOpen U) ≪≫
    (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology Z) U).symm

/-- The degree-zero identification `H'deltaFunctorZeroIso` cancels around the map induced by a
morphism of abelian sheaves, leaving the map it induces on sections. -/
@[reassoc]
theorem H'deltaFunctorZeroIso_inv_app_comp_map_comp_hom_app (U : TopologicalSpace.Opens Z)
    {A B : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}} (f : A ⟶ B) :
    (H'deltaFunctorZeroIso U).inv.app A ≫ ((H'deltaFunctor U).functor 0).map f ≫
        (H'deltaFunctorZeroIso U).hom.app B =
      (abSections U).map f := by
  rw [(H'deltaFunctorZeroIso U).hom.naturality f, Iso.inv_hom_id_app_assoc]

end Stacks.Cohomology.AbelianColimit

namespace Deformation.Artin.SectionsSheaf

open Stacks.Cohomology.AbelianColimit

/-- `abelianZeroIso` is `H'deltaFunctorZeroIso` at the whole space, precomposed with the
underlying abelian sheaf. -/
theorem abelianZeroIso_eq (X : Scheme.{u}) :
    abelianZeroIso X =
      Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf) (H'deltaFunctorZeroIso ⊤) :=
  rfl

/-! ### The edge map -/

section EdgeMap

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}} (p : X ⟶ Y) (π : Y ⟶ Spec R)

local notation "Ψ" =>
  Stacks.Cohomology.ModuleSpacePullback.underlyingPullback p.base Y.ringCatSheaf

/-- **The pullback of global sections along `p`**: a global section of an `𝒪_Y`-module `F` is
carried to its pullback, a global section of the abelian inverse image `p⁻¹ F_ab`. This is
`Stacks.Cohomology.ModuleSpacePullback.abSectionsPullback` at the whole spaces, written as a map
into `Ψ ⋙ Γ(X, -)` for `Ψ = p⁻¹ ∘ (-)_ab`. -/
def globalSectionsPullback :
    secF Y.ringCatSheaf ⊤ ⟶ Ψ ⋙ abSections (⊤ : TopologicalSpace.Opens X) :=
  Functor.whiskerLeft (SheafOfModules.toSheaf Y.ringCatSheaf)
      (Stacks.Cohomology.ModuleSpacePullback.abSectionsPullback p.base ⊤ ⊤ le_top) ≫
    (Functor.associator _ _ _).inv

/-- The degree-zero part of `pullbackHom`: the pullback of global sections, read between
`|H⁰_π(Y, F)|` and `H'⁰(X, p⁻¹ F_ab)`. -/
def pullbackZero :
    (abCohomology π).functor 0 ⟶
      ((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp Ψ).functor 0 :=
  (abCohomologyZeroIso π).hom ≫ globalSectionsPullback p ≫
    Functor.whiskerLeft Ψ (H'deltaFunctorZeroIso ⊤).inv

/-- **The pullback of cohomology along `p`, as a morphism of δ-functors on `𝒪_Y`-modules**:
`|Hⁿ_π(Y, F)| ⟶ H'ⁿ(X, p⁻¹ F_ab)`, the unique morphism of δ-functors extending the pullback of
global sections (Stacks 010S; `|Hⁿ_π(Y, -)|` is universal). -/
def pullbackHom : abCohomology π ⟶ (H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp Ψ :=
  DeltaFunctor.IsUniversal.lift _ (pullbackZero p π)

/-- In degree zero, `pullbackHom` is the pullback of global sections. -/
@[simp]
theorem pullbackHom_app_zero : (pullbackHom p π).app 0 = pullbackZero p π :=
  DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- `pullbackHom` is the only morphism of δ-functors that is the pullback of global sections in
degree zero. -/
theorem pullbackHom_unique
    (η : abCohomology π ⟶ (H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).precomp Ψ)
    (hη : η.app 0 = pullbackZero p π) : η = pullbackHom p π :=
  DeltaFunctor.IsUniversal.hom_ext_zero _ (hη.trans (pullbackHom_app_zero p π).symm)

/-- **The counit `p⁻¹ (p_* G)_ab ⟶ G_ab`** of the inverse-image/direct-image adjunction for
abelian sheaves, at the underlying abelian sheaf of an `𝒪_X`-module `G`; the underlying abelian
sheaf of `p_* G` is the abelian direct image of `G_ab`. -/
def pushforwardCounit : modulesPushforward p ⋙ Ψ ⟶ SheafOfModules.toSheaf X.ringCatSheaf :=
  Functor.whiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
    (Stacks.Cohomology.ExtComparison.Spaces.sheafAdjunction p.base).counit

/-- **The triangle identity on global sections**: pulling a global section of `p_* G` back to
`X` and applying the counit returns the same section of `G`, `Γ(Y, p_* G) = Γ(X, G)`. -/
theorem globalSectionsPullback_app_comp_map_pushforwardCounit_app
    (G : SheafOfModules.{u} X.ringCatSheaf) :
    (globalSectionsPullback p).app ((modulesPushforward p).obj G) ≫
        (abSections (⊤ : TopologicalSpace.Opens X)).map ((pushforwardCounit p).app G) =
      (pushforwardSecFIso p).hom.app G := by
  have hres : (sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map
      (homOfLE (le_top : (⊤ : TopologicalSpace.Opens X) ≤
        (TopologicalSpace.Opens.map p.base).obj ⊤)).op = 𝟙 _ := by
    rw [show homOfLE (le_top : (⊤ : TopologicalSpace.Opens X) ≤
        (TopologicalSpace.Opens.map p.base).obj ⊤) = 𝟙 _ from Subsingleton.elim _ _, op_id,
      CategoryTheory.Functor.map_id]
  have key := congrArg (fun f => (abSections (⊤ : TopologicalSpace.Opens Y)).map f)
    ((Stacks.Cohomology.ExtComparison.Spaces.sheafAdjunction p.base).right_triangle_components
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G))
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at key
  have hrc : ((sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map
        (homOfLE (le_top : (⊤ : TopologicalSpace.Opens X) ≤
          (TopologicalSpace.Opens.map p.base).obj ⊤)).op).app
          ((sheafPullback p.base).obj
            ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((modulesPushforward p).obj G))) ≫
        (Functor.associator (SheafOfModules.toSheaf Y.ringCatSheaf) (sheafPullback p.base)
          (abSections (⊤ : TopologicalSpace.Opens X))).inv.app ((modulesPushforward p).obj G) ≫
        (abSections (⊤ : TopologicalSpace.Opens X)).map ((pushforwardCounit p).app G) =
      (abSections (⊤ : TopologicalSpace.Opens Y)).map
        ((Stacks.Cohomology.ExtComparison.Spaces.sheafPushforward p.base).map
          ((Stacks.Cohomology.ExtComparison.Spaces.sheafAdjunction p.base).counit.app
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj G))) := by
    have h₁ : ((sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map
        (homOfLE (le_top : (⊤ : TopologicalSpace.Opens X) ≤
          (TopologicalSpace.Opens.map p.base).obj ⊤)).op).app
          ((sheafPullback p.base).obj
            ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((modulesPushforward p).obj G))) =
          𝟙 _ := by
      rw [hres, NatTrans.id_app]
    exact DeltaFunctor.id_comp_id_comp_eq h₁ (Functor.associator_inv_app _ _ _ _) rfl
  exact DeltaFunctor.comp_comp_comp_eq hrc key

/-- **The Leray edge map** `|Hⁿ_π(Y, p_* G)| ⟶ |Hⁿ_{p ≫ π}(X, G)|`, natural in the `𝒪_X`-module
`G`: the pullback of cohomology along `p` at `p_* G`, followed by the counit
`p⁻¹ (p_* G)_ab ⟶ G_ab` in cohomology and by the inverse of the comparison
`|Hⁿ(X, G)| ≅ H'ⁿ(X, G_ab)` of Stacks 03FD. -/
def edgeMap (n : ℕ) :
    modulesPushforward p ⋙ (abCohomology π).functor n ⟶ (abCohomology (p ≫ π)).functor n :=
  DeltaFunctor.edgeHom (pullbackHom p π) (pushforwardCounit p) (abelianIso (p ≫ π)).inv n

/-- The components of the edge map. -/
theorem edgeMap_app (n : ℕ) (G : SheafOfModules.{u} X.ringCatSheaf) :
    (edgeMap p π n).app G =
      ((pullbackHom p π).app n).app ((modulesPushforward p).obj G) ≫
        ((H'deltaFunctor (⊤ : TopologicalSpace.Opens X)).functor n).map
          ((pushforwardCounit p).app G) ≫
          ((abelianIso (p ≫ π)).inv.app n).app G :=
  DeltaFunctor.edgeHom_app _ _ _ n G

/-- **The edge map commutes with the connecting morphisms**: for a short exact sequence `S` of
`𝒪_X`-modules whose direct image `p_* S` is short exact, the edge map carries the connecting
morphism of `|H(Y, -)|` at `p_* S` to that of `|H(X, -)|` at `S`. -/
theorem edgeMap_δ {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (hpS : (S.map (modulesPushforward p)).ShortExact) (n : ℕ) :
    (edgeMap p π n).app S.X₃ ≫ (abCohomology (p ≫ π)).δ hS n =
      (abCohomology π).δ hpS n ≫ (edgeMap p π (n + 1)).app S.X₁ :=
  DeltaFunctor.edgeHom_comp_δ _ _ _ hS hpS n

/-- **The edge map is the identity on global sections in degree zero**, componentwise:
`Γ(Y, p_* G) = Γ(X, G)`, read through `abCohomologyZeroIso` on both sides. -/
theorem edgeMap_app_zero (G : SheafOfModules.{u} X.ringCatSheaf) :
    (edgeMap p π 0).app G =
      (abCohomologyZeroIso π).hom.app ((modulesPushforward p).obj G) ≫
        (pushforwardSecFIso p).hom.app G ≫ (abCohomologyZeroIso (p ≫ π)).inv.app G :=
  DeltaFunctor.edgeHom_app_zero (pullbackHom p π) (pushforwardCounit p) (abelianIso (p ≫ π)).inv
    (abCohomologyZeroIso π) (abCohomologyZeroIso (p ≫ π)) (H'deltaFunctorZeroIso ⊤)
    (globalSectionsPullback p) (pushforwardSecFIso p).hom (pullbackHom_app_zero p π)
    (by rw [abelianIso_inv_app_zero, abelianZeroIso_eq, Functor.isoWhiskerLeft_hom]; rfl)
    (globalSectionsPullback_app_comp_map_pushforwardCounit_app p) G

/-- **The edge map is the identity on global sections in degree zero**: `Γ(Y, p_* G) = Γ(X, G)`,
read through `abCohomologyZeroIso` on both sides. -/
theorem edgeMap_zero :
    edgeMap p π 0 =
      Functor.whiskerLeft (modulesPushforward p) (abCohomologyZeroIso π).hom ≫
        (pushforwardSecFIso p).hom ≫ (abCohomologyZeroIso (p ≫ π)).inv := by
  ext G : 2
  exact edgeMap_app_zero p π G

/-- The edge map carries the class in `|H⁰(Y, p_* G)|` of a global section to the class in
`|H⁰(X, G)|` of the same section. -/
@[reassoc]
theorem abCohomologyZeroIso_inv_app_comp_edgeMap_app (G : SheafOfModules.{u} X.ringCatSheaf) :
    (abCohomologyZeroIso π).inv.app ((modulesPushforward p).obj G) ≫ (edgeMap p π 0).app G =
      (pushforwardSecFIso p).hom.app G ≫ (abCohomologyZeroIso (p ≫ π)).inv.app G := by
  rw [edgeMap_app_zero, Iso.inv_hom_id_app_assoc]

/-- The edge map in degree zero, on elements. -/
theorem edgeMap_app_zero_apply (G : SheafOfModules.{u} X.ringCatSheaf)
    (s : ((secF X.ringCatSheaf ⊤).obj G : Type u)) :
    (edgeMap p π 0).app G ((abCohomologyZeroIso π).inv.app ((modulesPushforward p).obj G) s) =
      (abCohomologyZeroIso (p ≫ π)).inv.app G s :=
  ConcreteCategory.congr_hom (abCohomologyZeroIso_inv_app_comp_edgeMap_app p π G) s

section Iso

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- An `𝒪_X`-module with vanishing higher direct images is the first term of a short exact
sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` with `I` injective, kept exact by `p_*`, whose second and third
terms again have vanishing higher direct images, and whose middle term has acyclic direct image
(Stacks 01EX, part (2)). -/
private theorem exists_effacement (G : SheafOfModules.{u} X.ringCatSheaf)
    (hG : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj G)) :
    ∃ (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) (_ : S.ShortExact)
      (_ : (S.map (modulesPushforward p)).ShortExact), Nonempty (S.X₁ ≅ G) ∧
      (∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj S.X₂)) ∧
      (∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj S.X₃)) ∧
      (∀ n, IsZero (((abCohomology π).functor (n + 1)).obj ((modulesPushforward p).obj S.X₂))) ∧
      ∀ n, IsZero (((abCohomology (p ≫ π)).functor (n + 1)).obj S.X₂) := by
  have hI : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj (Injective.under G)) := by
    intro q hq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hq
    have : Injective (C := X.Modules) (Injective.under G) :=
      inferInstanceAs (Injective (C := SheafOfModules.{u} X.ringCatSheaf) (Injective.under G))
    simpa using (Scheme.Modules.pushforward p).isZero_rightDerived_obj_injective_succ k
      (Injective.under G)
  have hS : (ShortComplex.cokernelSequence (Injective.ι G)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact (Injective.ι G)
      mono_f := inferInstanceAs (Mono (Injective.ι G))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι G))) }
  have hac := fun A => Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
    (modulesPushforward p) A
  obtain ⟨hQ, hpS⟩ := (Functor.rightAcyclic_and_shortExact_map_of_shortExact
    (modulesPushforward p) _ hS).2.1 ((hac G).2 hG) ((hac (Injective.under G)).2 hI)
  exact ⟨_, hS, hpS, ⟨Iso.refl G⟩, hI, (hac _).1 hQ,
    fun n => isZero_abCohomology_obj_of_rightAcyclic π
      (rightAcyclic_modulesPushforward_obj p (Injective.under G)) n,
    fun n => (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero
      ((sectionsOverBase (p ≫ π)).isZero_rightDerived_obj_injective_succ n (Injective.under G))⟩

/-- **Stacks 01F4, part (1), through the edge map.** If the higher direct images `R^q p_* G`
vanish for `q > 0`, the edge map `|Hⁿ(Y, p_* G)| ⟶ |Hⁿ(X, G)|` is an isomorphism in every
degree. -/
@[stacks 01F4 "(1) for a morphism of schemes, the isomorphism H^p(Y, f_*F) ≅ H^p(X, F) being the
edge map, which commutes with the connecting morphisms"]
theorem isIso_edgeMap_app (G : SheafOfModules.{u} X.ringCatSheaf)
    (hG : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj G))
    (n : ℕ) : IsIso ((edgeMap p π n).app G) :=
  DeltaFunctor.isIso_app_of_comp_δ (edgeMap p π) (edgeMap_δ p π)
    (fun G => ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj G))
    (fun G _ => by rw [edgeMap_app_zero]; infer_instance)
    (fun G hG => exists_effacement p π G hG) n G hG

/-- **The edge map is unique**: a family of natural transformations
`p_* ⋙ |Hⁿ_π(Y, -)| ⟶ |Hⁿ_{p ≫ π}(X, -)|` that is the identity on global sections in degree zero
and commutes with the connecting morphisms of every short exact sequence kept exact by `p_*` is
the edge map at every `𝒪_X`-module with vanishing higher direct images. -/
theorem app_eq_edgeMap_app
    (ε : ∀ n, modulesPushforward p ⋙ (abCohomology π).functor n ⟶
      (abCohomology (p ≫ π)).functor n)
    (hε : ∀ {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
      (hpS : (S.map (modulesPushforward p)).ShortExact) (n : ℕ),
      (ε n).app S.X₃ ≫ (abCohomology (p ≫ π)).δ hS n =
        (abCohomology π).δ hpS n ≫ (ε (n + 1)).app S.X₁)
    (h₀ : ∀ G : SheafOfModules.{u} X.ringCatSheaf,
      (abCohomologyZeroIso π).inv.app ((modulesPushforward p).obj G) ≫ (ε 0).app G =
        (pushforwardSecFIso p).hom.app G ≫ (abCohomologyZeroIso (p ≫ π)).inv.app G)
    (G : SheafOfModules.{u} X.ringCatSheaf)
    (hG : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj G))
    (n : ℕ) : (ε n).app G = (edgeMap p π n).app G :=
  DeltaFunctor.app_eq_of_comp_δ ε (edgeMap p π) hε (edgeMap_δ p π)
    (fun G => ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj G))
    (fun G _ => (cancel_epi ((abCohomologyZeroIso π).inv.app ((modulesPushforward p).obj G))).1
      ((h₀ G).trans (abCohomologyZeroIso_inv_app_comp_edgeMap_app p π G).symm))
    (fun G hG => by
      obtain ⟨S, hS, hpS, e, -, h₃, hD, -⟩ := exists_effacement p π G hG
      exact ⟨S, hS, hpS, e, h₃, hD⟩) n G hG

end Iso

/-- **Stacks 01F4, part (1), for an affine morphism and a quasi-coherent module**: the higher
direct images vanish (Stacks 01XC), so the edge map is an isomorphism. -/
theorem isIso_edgeMap_app_of_isQuasicoherent [IsAffineHom p]
    (G : SheafOfModules.{u} X.ringCatSheaf) [G.IsQuasicoherent] (n : ℕ) :
    IsIso ((edgeMap p π n).app G) :=
  isIso_edgeMap_app p π G
    (fun q hq => Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward p G q hq) n

/-- **The edge isomorphism** `|Hⁿ(Y, p_* G)| ≅ |Hⁿ(X, G)|` for `p` affine and `G`
quasi-coherent. -/
def edgeIso [IsAffineHom p] (G : SheafOfModules.{u} X.ringCatSheaf) [G.IsQuasicoherent]
    (n : ℕ) :
    ((abCohomology π).functor n).obj ((modulesPushforward p).obj G) ≅
      ((abCohomology (p ≫ π)).functor n).obj G :=
  haveI := isIso_edgeMap_app_of_isQuasicoherent p π G n
  asIso ((edgeMap p π n).app G)

/-- The edge isomorphism is the edge map. -/
@[simp]
theorem edgeIso_hom [IsAffineHom p] (G : SheafOfModules.{u} X.ringCatSheaf) [G.IsQuasicoherent]
    (n : ℕ) : (edgeIso p π G n).hom = (edgeMap p π n).app G :=
  rfl

section Exact

variable [PreservesFiniteColimits (modulesPushforward p)]

/-- **The edge map along an exact direct image is a morphism of δ-functors**: when `p_*` is
exact (a closed immersion, for instance), `G ↦ |Hⁿ(Y, p_* G)|` is a δ-functor and the edge map
commutes with all of its connecting morphisms. -/
def edgeDeltaHom : abCohomologyPushforward π p ⟶ abCohomology (p ≫ π) where
  app n := edgeMap p π n
  comm hS n := by
    rw [abCohomologyPushforward_δ π p hS (hS.map_of_exact _)]
    exact edgeMap_δ p π hS _ n

/-- **Along an exact direct image the edge map is `thickeningIso`**: both are morphisms of
δ-functors out of a universal δ-functor that are the identity on global sections in degree
zero. -/
theorem edgeDeltaHom_eq_thickeningIso : edgeDeltaHom p π = (thickeningIso π p (p ≫ π)).hom :=
  thickeningIso_unique π p (p ≫ π) _ (edgeMap_zero p π)

end Exact

end EdgeMap

/-! ### The edge map of a composite with an exact direct image -/

section Composite

variable {R : CommRingCat.{u}} {X' X Y : Scheme.{u}} (i : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y)
  (hp : i ≫ p = p') (π : Y ⟶ Spec R)

/-- **`p'_* ≅ p_* ∘ i_*` for `i ≫ p = p'`**: Mathlib's `Scheme.Modules.pushforwardComp`, after
the equality `p'_* = (i ≫ p)_*`. Stating it for `p'` propositionally equal to `i ≫ p` lets the
composite be a projection `W_{T'} ⟶ W` rather than its factorization through `W_T`. -/
def modulesPushforwardCompIso :
    modulesPushforward p' ≅ modulesPushforward i ⋙ modulesPushforward p :=
  eqToIso (congrArg modulesPushforward hp.symm) ≪≫ (Scheme.Modules.pushforwardComp i p).symm

/-- `modulesPushforwardCompIso` is the identity on global sections:
`Γ(Y, p'_* G) = Γ(Y, p_* i_* G) = Γ(X, i_* G) = Γ(X', G)`. -/
theorem pushforwardSecFIso_comp (G : SheafOfModules.{u} X'.ringCatSheaf) :
    (secF Y.ringCatSheaf ⊤).map ((modulesPushforwardCompIso i p p' hp).hom.app G) ≫
        (pushforwardSecFIso p).hom.app ((modulesPushforward i).obj G) ≫
          (pushforwardSecFIso i).hom.app G =
      (pushforwardSecFIso p').hom.app G := by
  subst hp
  rfl

variable [PreservesFiniteColimits (modulesPushforward i)]

/-- **The edge map of `p' = i ≫ p` through the edge map of `p`**, for `i` with exact direct
image (a closed immersion): at an `𝒪_{X'}`-module `G` with vanishing higher direct images along
`p'`, the edge map of `p'` is `p'_* G ≅ p_* i_* G`, then the edge map of `p` at `i_* G`, then the
comparison `|Hⁿ(X, i_* G)| ≅ |Hⁿ(X', G)|` of `thickeningIso`. Both sides commute with the
connecting morphisms on sequences kept exact by `p'_*` and are the identity on global sections in
degree zero, so this is `app_eq_edgeMap_app`. -/
theorem edgeMap_app_eq_of_comp_eq (G : SheafOfModules.{u} X'.ringCatSheaf)
    (hG : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p').rightDerived q).obj G))
    (n : ℕ) :
    (edgeMap p' π n).app G =
      ((abCohomology π).functor n).map ((modulesPushforwardCompIso i p p' hp).hom.app G) ≫
        (edgeMap p π n).app ((modulesPushforward i).obj G) ≫
          ((thickeningIso (p ≫ π) i (p' ≫ π)).hom.app n).app G := by
  have key := app_eq_edgeMap_app p' π
    (DeltaFunctor.compAlong (modulesPushforwardCompIso i p p' hp) (edgeMap p π)
      (fun n => (thickeningIso (p ≫ π) i (p' ≫ π)).hom.app n))
    (fun hS hpS n => DeltaFunctor.compAlong_comp_δ (modulesPushforwardCompIso i p p' hp)
      (edgeMap p π) (fun n => (thickeningIso (p ≫ π) i (p' ≫ π)).hom.app n) (edgeMap_δ p π)
      (thickeningIso_hom_comp_δ (p ≫ π) i (p' ≫ π)) (fun hS => hS.map_of_exact _) hS hpS n)
    (DeltaFunctor.compAlong_app_zero (modulesPushforwardCompIso i p p' hp) (edgeMap p π)
      (fun n => (thickeningIso (p ≫ π) i (p' ≫ π)).hom.app n) (abCohomologyZeroIso π)
      (abCohomologyZeroIso (p ≫ π)) (abCohomologyZeroIso (p' ≫ π)) (pushforwardSecFIso p).hom
      (pushforwardSecFIso i).hom (pushforwardSecFIso p').hom
      (abCohomologyZeroIso_inv_app_comp_edgeMap_app p π)
      (abCohomologyZeroIso_inv_app_comp_thickeningIso_hom_app (p ≫ π) i (p' ≫ π))
      (pushforwardSecFIso_comp i p p' hp))
    G hG n
  exact key.symm.trans (DeltaFunctor.compAlong_app _ _ _ n G)

end Composite

/-- **The edge map of a composite with a closed immersion**: for a closed immersion
`i : X' ⟶ X`, a morphism `p : X ⟶ Y` and an `𝒪_{X'}`-module `G` with vanishing higher direct
images along `i ≫ p`, the edge map of `i ≫ p` at `G` is the edge map of `p` at `i_* G` followed by
the comparison `thickeningIso` of the cohomology of `X` and `X'`. -/
theorem edgeMap_comp_closedImmersion {R : CommRingCat.{u}} {X' X Y : Scheme.{u}} (i : X' ⟶ X)
    [IsClosedImmersion i] (p : X ⟶ Y) (π : Y ⟶ Spec R) (G : SheafOfModules.{u} X'.ringCatSheaf)
    (hG : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward (i ≫ p)).rightDerived q).obj G))
    (n : ℕ) :
    (edgeMap (i ≫ p) π n).app G =
      ((abCohomology π).functor n).map
          ((modulesPushforwardCompIso i p (i ≫ p) rfl).hom.app G) ≫
        (edgeMap p π n).app ((modulesPushforward i).obj G) ≫
          ((thickeningIso (p ≫ π) i ((i ≫ p) ≫ π)).hom.app n).app G :=
  edgeMap_app_eq_of_comp_eq i p (i ≫ p) rfl π G hG n

/-- **The edge map of `W_{T'} ⟶ W` through that of `W_T ⟶ W`**: for a morphism `α : T' ⟶ T` of
schemes over `S` whose base change `W_{T'} ⟶ W_T` along `q : W ⟶ S` is a closed immersion (a
thickening, for the quotient map of a deformation situation), an affine projection
`W_{T'} ⟶ W` and a quasi-coherent `𝒪_{W_{T'}}`-module `G`, the edge map of `W_{T'} ⟶ W` at `G`
is the edge map of `W_T ⟶ W` at the direct image of `G` followed by `thickeningIso`. -/
theorem edgeMap_app_pullback_snd {R : CommRingCat.{u}} {S W : Scheme.{u}} (q : W ⟶ S)
    {T T' : Over S} (α : T' ⟶ T) [IsClosedImmersion (baseChangeMap q α)]
    [IsAffineHom (pullback.snd T'.hom q)] (π : W ⟶ Spec R)
    (G : SheafOfModules.{u} (pullback T'.hom q).ringCatSheaf) [G.IsQuasicoherent] (n : ℕ) :
    (edgeMap (pullback.snd T'.hom q) π n).app G =
      ((abCohomology π).functor n).map
          ((modulesPushforwardCompIso (baseChangeMap q α) (pullback.snd T.hom q)
            (pullback.snd T'.hom q) (baseChangeMap_comp_snd q α)).hom.app G) ≫
        (edgeMap (pullback.snd T.hom q) π n).app
          ((modulesPushforward (baseChangeMap q α)).obj G) ≫
          ((thickeningIso (pullback.snd T.hom q ≫ π) (baseChangeMap q α)
            (pullback.snd T'.hom q ≫ π)).hom.app n).app G :=
  edgeMap_app_eq_of_comp_eq (baseChangeMap q α) (pullback.snd T.hom q) (pullback.snd T'.hom q)
    (baseChangeMap_comp_snd q α) π G
    (fun k hk => Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward _ G k hk) n

end Deformation.Artin.SectionsSheaf

end
