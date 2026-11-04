module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexSquareOpens
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrictDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalGlueing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartExistence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexGenuineFamily
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedPullbackOpensObjectGlueing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal

/-!
# Existence of relative dualizing complexes

Let `f : X ⟶ S` be flat and locally of finite presentation and let `W ⊆ X ×_S X` be an open
through which the relative diagonal factors as a closed immersion `Δ : X ⟶ W`. This file proves
Stacks 0E2X: there is a relative dualizing complex `(K, ξ)` (Stacks 0E2T) relative to `W`.

Following the source, let `ℬ` be the affine opens of `X` mapping into an affine open of `S`. For
`U ∈ ℬ` the open `W_U = W ∩ (U ×_S U)` of `W` is a diagonal open of `U ⟶ S`, and the chart step
(Stacks 0E2F through Stacks 0E2U) gives a relative dualizing complex `(K_U, ξ_U)` on it. For
`V ⊆ U` in `ℬ`, transporting `ξ_U` to `W_V` makes `K_U|_V` a relative dualizing complex for
`V ⟶ S`, so Stacks 0E2W gives a unique `ρ^U_V : K_U|_V ≅ K_V` carrying the transported `ξ_U` to
`ξ_V`; uniqueness gives the cocycle condition, and the BBD glueing lemma (Stacks 0D6C, with the
negative self-`Ext` of Stacks 0E2V) glues the `K_U` to `K` with `σ_U : K|_U ≅ K_U`. The maps
`ξ_U`, read on `W_U` through `σ_U`, are compatible on the overlaps; they glue to
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` by Stacks 0D66 on the covering of `W` by the charts `W_U` and the
opens missing `Δ(X)` (on which `Δ_*𝒪_X` vanishes), the negative `Ext` from `Δ_*𝒪_X` to
`L pr₁^*K|_W` vanishing on the charts by Stacks 0A76. Both conditions of Stacks 0E2T are local
(relative perfectness on `X`, the diagonal condition near `Δ(X)`), and hold on the charts.

The source changes `W` to the union of the opens `U ×_S U`; here the glueing is done on the given
`W` directly, the opens missing `Δ(X)` completing the covering.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isRelativeDualizingComplex`: **Stacks 0E2X**.
* `AlgebraicGeometry.Scheme.Hom.exists_isRelativeDualizingComplex_canonicalFamily`: the same at
  the canonical families of derived tensor products.
* `AlgebraicGeometry.Scheme.Hom.exists_glueing_chart`: the BBD step.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_hom_of_squareOpens`: glueing morphisms out of
  `Δ_*𝒪_X` from the charts.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_iso_comp`: the diagonal
  condition does not see automorphisms of `Δ_*𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.subsingleton_shiftedHom_diagonalObject`: no negative
  `Ext` from `Δ_*𝒪_X` to `L pr₁^*K|_W` for a relative dualizing complex.

## Implementation notes

The transport of `ξ_U` from `W_U` to `W_V` identifies the two diagonal objects through
`Δ_*𝒪_X` restricted from `W`, not through the base change square of `W_V ⊆ W_U`. With that choice
transporting twice is transporting once by the coherence of the composition isomorphisms of
derived pullback alone (`DiagonalOpen.squareTransport_squareTransport`), and the transported pair
is still a relative dualizing complex because the diagonal condition does not see automorphisms
of `Δ_*𝒪_X`. The diagram chases are lemmas in which every object and morphism is a variable,
applied as terms.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which the chart step, the restriction of relative dualizing complexes and Stacks 0E2W are stated.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.5 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Lemma 48.28.3 (Tag 0E2V)](https://stacks.math.columbia.edu/tag/0E2V)
* [Stacks Project, Theorem 20.45.8 (Tag 0D6C)](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

/-! ### Coherence of the composition isomorphisms of derived pullback around two squares -/

namespace Stacks.DerivedPullback

attribute [local instance 10000] HasDerivedCategory.standard

variable {A₁ A₂ A₃ B₁ B₂ B₃ : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The chase behind `factorIso_square_paste`, with every object and isomorphism a variable. -/
theorem paste_chase {C : Type*} [Category C] {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ : C}
    (α₁ : T₁ ≅ T₂) (α₂ : T₂ ≅ T₃) (m₁ : T₁ ≅ T₄) (x : T₄ ≅ T₃) (m₂ : T₅ ≅ T₄)
    (β₁ : T₅ ≅ T₆) (y : T₆ ≅ T₃) (γ₁ : T₇ ≅ T₆) (m₃ : T₇ ≅ T₈) (z : T₈ ≅ T₃)
    (hα : α₁.hom ≫ α₂.hom = m₁.hom ≫ x.hom) (hβ : β₁.hom ≫ y.hom = m₂.hom ≫ x.hom)
    (hγ : γ₁.hom ≫ y.hom = m₃.hom ≫ z.hom) :
    α₁.inv ≫ (m₁.hom ≫ m₂.inv) ≫ (β₁.hom ≫ γ₁.inv) ≫ m₃.hom = α₂.hom ≫ z.inv := by
  have h₁ := x.eq_comp_inv.2 hα.symm
  have h₂' := x.eq_comp_inv.2 hβ.symm
  have h₂ : m₂.inv = x.hom ≫ y.inv ≫ β₁.inv := by
    apply (cancel_epi m₂.hom).1
    rw [Iso.hom_inv_id, h₂']
    simp
  have h₃ : γ₁.inv ≫ m₃.hom = y.hom ≫ z.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hγ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h₁, h₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h₃, Iso.inv_hom_id_assoc]

/-- `paste_chase`, for isomorphisms. -/
theorem paste_chase_iso {C : Type*} [Category C] {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ : C}
    (α₁ : T₁ ≅ T₂) (α₂ : T₂ ≅ T₃) (m₁ : T₁ ≅ T₄) (x : T₄ ≅ T₃) (m₂ : T₅ ≅ T₄)
    (β₁ : T₅ ≅ T₆) (y : T₆ ≅ T₃) (γ₁ : T₇ ≅ T₆) (m₃ : T₇ ≅ T₈) (z : T₈ ≅ T₃)
    (hα : α₁ ≪≫ α₂ = m₁ ≪≫ x) (hβ : β₁ ≪≫ y = m₂ ≪≫ x) (hγ : γ₁ ≪≫ y = m₃ ≪≫ z) :
    α₁.symm ≪≫ (m₁ ≪≫ m₂.symm) ≪≫ (β₁ ≪≫ γ₁.symm) ≪≫ m₃ = α₂ ≪≫ z.symm :=
  Iso.ext (paste_chase α₁ α₂ m₁ x m₂ β₁ y γ₁ m₃ z (congrArg Iso.hom hα) (congrArg Iso.hom hβ)
    (congrArg Iso.hom hγ))

/-- `paste_chase_iso` with the two squares given by their two halves, and the pullback of the
first square along a functor. -/
theorem paste_chase_fun {C₂ C₃ E : Type*} [Category C₂] [Category C₃] [Category E]
    (G : C₂ ⥤ C₃) (H : E ⥤ C₃) {U₁ U₂ U₃ : C₂} (A₂₁ : U₁ ≅ U₂) (B₂₁ : U₃ ≅ U₂) (P₂₁ : U₁ ≅ U₃)
    (hP₂₁ : P₂₁ = A₂₁ ≪≫ B₂₁.symm) {E₁ E₂ : E} (J : E₁ ≅ E₂) {T₂ T₃ T₆ : C₃}
    (α₁ : G.obj U₁ ≅ T₂) (α₂ : T₂ ≅ T₃) (x : G.obj U₂ ≅ T₃) (β₁ : G.obj U₃ ≅ T₆) (y : T₆ ≅ T₃)
    (γ₁ : H.obj E₁ ≅ T₆) (z : H.obj E₂ ≅ T₃) (P₃₂ : G.obj U₃ ≅ H.obj E₁)
    (hP₃₂ : P₃₂ = β₁ ≪≫ γ₁.symm) (P₃₁ : T₂ ≅ H.obj E₂) (hP₃₁ : P₃₁ = α₂ ≪≫ z.symm)
    (hα : α₁ ≪≫ α₂ = G.mapIso A₂₁ ≪≫ x) (hβ : β₁ ≪≫ y = G.mapIso B₂₁ ≪≫ x)
    (hγ : γ₁ ≪≫ y = H.mapIso J ≪≫ z) :
    α₁.symm ≪≫ G.mapIso P₂₁ ≪≫ P₃₂ ≪≫ H.mapIso J = P₃₁ := by
  subst hP₂₁ hP₃₂ hP₃₁
  rw [Functor.mapIso_trans, Functor.mapIso_symm]
  exact paste_chase_iso α₁ α₂ (G.mapIso A₂₁) x (G.mapIso B₂₁) β₁ y γ₁ (H.mapIso J) z hα hβ hγ

/-- The chase comparing a morphism on `W_U` restricted to `W_V` with its transport between the
charts, with every object and isomorphism a variable. -/
theorem restrict_transport_chase {C₁ C₂ : Type*} [Category C₁] [Category C₂] (G : C₁ ⥤ C₂)
    {A_U Δ_U L_U P_U : C₁} {A_V Δ_V L_V Q P_V : C₂} (eU : A_U ≅ Δ_U) (eV : A_V ≅ Δ_V)
    (cΔ : G.obj A_U ≅ A_V) (cL cL' : G.obj L_U ≅ L_V) (hcL : cL = cL') (pU : L_U ≅ P_U)
    (pV : L_V ≅ P_V) (T : G.obj P_U ≅ Q) (R R' : Q ≅ P_V) (hR : R = R')
    (hP : cL'.symm ≪≫ G.mapIso pU ≪≫ T ≪≫ R' = pV) (α : A_U ⟶ L_U) :
    ((G.mapIso eU.symm ≪≫ cΔ ≪≫ eV).inv ≫ G.map (eU.inv ≫ α ≫ pU.hom) ≫ T.hom) ≫ R.hom =
      eV.inv ≫ (cΔ.inv ≫ G.map α ≫ cL.hom) ≫ pV.hom := by
  subst hcL hR hP
  simp

/-- The chase showing that transporting twice between charts is transporting once, with every
object and isomorphism a variable. -/
theorem transport_comp_chase {C₁ C₂ C₃ E : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category E] (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₁ ⥤ C₃) (κ : G₁ ⋙ G₂ ≅ G₃) (H : E ⥤ C₃)
    {A_U Δ_U L_U : C₁} {A_V Δ_V L_V : C₂} {A_W Δ_W : C₃} (eU : A_U ≅ Δ_U) (eV : A_V ≅ Δ_V)
    (eW : A_W ≅ Δ_W) (c₁ : G₁.obj A_U ≅ A_V) (c₂ : G₂.obj A_V ≅ A_W) (c₃ : G₃.obj A_U ≅ A_W)
    (kA : G₂.obj (G₁.obj A_U) ≅ G₃.obj A_U) (hkA : kA = κ.app A_U)
    (hc : kA.hom ≫ c₃.hom = G₂.map c₁.hom ≫ c₂.hom) {E₁ E₂ : E}
    (P₁ : G₁.obj L_U ≅ L_V) (P₂ : G₂.obj L_V ≅ H.obj E₁) (P₃ : G₃.obj L_U ≅ H.obj E₂)
    (J J' : E₁ ≅ E₂) (hJ : J = J')
    (hP : (κ.app L_U).symm ≪≫ G₂.mapIso P₁ ≪≫ P₂ ≪≫ H.mapIso J' = P₃) (ζ : Δ_U ⟶ L_U) :
    ((G₂.mapIso eV.symm ≪≫ c₂ ≪≫ eW).inv ≫
        G₂.map ((G₁.mapIso eU.symm ≪≫ c₁ ≪≫ eV).inv ≫ G₁.map ζ ≫ P₁.hom) ≫ P₂.hom) ≫ H.map J.hom =
      (G₃.mapIso eU.symm ≪≫ c₃ ≪≫ eW).inv ≫ G₃.map ζ ≫ P₃.hom := by
  subst hJ hP hkA
  have hc' : c₂.inv ≫ G₂.map c₁.inv = c₃.inv ≫ κ.inv.app A_U := by
    have := congrArg Iso.inv (Iso.ext (α := κ.app A_U ≪≫ c₃) (β := G₂.mapIso c₁ ≪≫ c₂) hc)
    simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] at this
    exact this.symm
  have hn : ∀ {A B : C₁} (y : A ⟶ B) {Z : C₃} (k : G₂.obj (G₁.obj B) ⟶ Z),
      κ.inv.app A ≫ G₂.map (G₁.map y) ≫ k = G₃.map y ≫ κ.inv.app B ≫ k :=
    fun y _ k => by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ k) (κ.inv.naturality y).symm
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id_assoc, reassoc_of% hc', hn]

/-- Conjugating a composite by a natural square, with every object a variable. -/
theorem conj_map_comp {C₁ C₂ : Type*} [Category C₁] [Category C₂] (G : C₁ ⥤ C₂)
    {A : C₂} {B M N : C₁} {PM PN : C₂} (a : A ⟶ G.obj B) (ζ : B ⟶ M) (x : M ⟶ N)
    (pM : G.obj M ⟶ PM) (pN : G.obj N ⟶ PN) (y : PM ⟶ PN) (hn : G.map x ≫ pN = pM ≫ y) :
    a ≫ G.map (ζ ≫ x) ≫ pN = (a ≫ G.map ζ ≫ pM) ≫ y := by
  rw [G.map_comp, Category.assoc, hn, Category.assoc, Category.assoc]

/-- Inserting `e⁻¹ ≫ e`, with every object a variable. -/
theorem trans_symm_hom_comp {C : Type*} [Category C] {A B B' P : C} (ε : B ≅ A) (e : B ≅ B')
    (k : B ⟶ P) : ε.inv ≫ k = (ε.symm ≪≫ e).hom ≫ (e.inv ≫ k) := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The cocycle chase of the proof of Stacks 0E2X, with every object a variable. -/
theorem cocycle_chase {C E : Type*} [Category C] [Category E] (H : E ⥤ C) {Δ : C}
    {A₁ A₂ A₃ B : E} (x : Δ ⟶ H.obj A₁) (y : Δ ⟶ H.obj A₂) (z : Δ ⟶ H.obj A₃) (w : Δ ⟶ H.obj B)
    (t : A₁ ≅ A₂) (a : A₁ ⟶ A₃) (b : A₃ ⟶ B) (hy : x ≫ H.map t.hom = y) (hx : x ≫ H.map a = z)
    (hz : z ≫ H.map b = w) : y ≫ H.map (t.inv ≫ a ≫ b) = w := by
  rw [← hy, ← hz, ← hx]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]

/-- Solving the compatibility of a glueing for the transition isomorphism, with every object a
variable. -/
theorem glueing_chase {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {A B : C} {P R : D}
    (c : G.obj A ≅ P) (sU : A ≅ B) (sV : P ≅ R) (ρ : G.obj B ≅ R)
    (hσ : c.inv ≫ G.map sU.hom ≫ ρ.hom = sV.hom) : G.map sU.inv ≫ c.hom ≫ sV.hom = ρ.hom := by
  rw [← hσ, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp

/-- Cancelling the identifications around a chart map, with every object a variable. -/
theorem conj_cancel_chase {C : Type*} [Category C] {A Δ L P Q : C} (e : A ≅ Δ) (p : L ≅ P)
    (x₁ : Δ ⟶ Q) (x₂ : Q ⟶ P) : e.inv ≫ (e.hom ≫ x₁ ≫ x₂ ≫ p.inv) ≫ p.hom = x₁ ≫ x₂ := by
  simp

/-- The compatibility of the chart maps of the proof of Stacks 0E2X, with every object a
variable. -/
theorem chart_compat_chase {C E : Type*} [Category C] [Category E] (H : E ⥤ C) {A' Δ' L' : C}
    {N M₁ M₂ M₃ : E} (eV : A' ≅ Δ') (pV : L' ≅ H.obj M₂) (r : A' ⟶ L') (τζ : Δ' ⟶ H.obj M₁)
    (τξ : Δ' ⟶ H.obj N) (a : N ⟶ M₁) (hτ : τζ = τξ ≫ H.map a) (c : M₁ ⟶ M₂)
    (hres : τζ ≫ H.map c = eV.inv ≫ r ≫ pV.hom) (sV : M₂ ≅ M₃) (ξV : Δ' ⟶ H.obj M₃)
    (hglue : τξ ≫ H.map (a ≫ c ≫ sV.hom) = ξV) : r = eV.hom ≫ ξV ≫ H.map sV.inv ≫ pV.inv := by
  have h₁ : r = eV.hom ≫ (τζ ≫ H.map c) ≫ pV.inv := by rw [hres]; simp
  rw [h₁, hτ, ← hglue]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]

/-- **Two commutative squares of derived pullbacks paste.** Given squares `a₂₁ ≫ p₁ = p₂ ≫ b₂₁`
and `a₃₂ ≫ p₂ = p₃ ≫ b₃₂` and their composite `a₃₁ ≫ p₁ = p₃ ≫ b₃₁`, the comparison
`La₂₁^* Lp₁^* ≅ Lp₂^* Lb₂₁^*` of the first square, pulled back along `a₃₂` and followed by the
comparison of the second square, is the comparison of the composite square, up to the
composition isomorphisms of `a₃₂ ≫ a₂₁ = a₃₁` and `b₃₂ ≫ b₂₁ = b₃₁`. -/
theorem factorIso_square_paste (p₁ : A₁ ⟶ B₁) (p₂ : A₂ ⟶ B₂) (p₃ : A₃ ⟶ B₃)
    (a₂₁ : A₂ ⟶ A₁) (a₃₂ : A₃ ⟶ A₂) (a₃₁ : A₃ ⟶ A₁) (b₂₁ : B₂ ⟶ B₁) (b₃₂ : B₃ ⟶ B₂)
    (b₃₁ : B₃ ⟶ B₁) (q₂₁ : A₂ ⟶ B₁) (q₃₂ : A₃ ⟶ B₂) (q₃₁ : A₃ ⟶ B₁)
    (ha : a₃₂ ≫ a₂₁ = a₃₁) (hb : b₃₂ ≫ b₂₁ = b₃₁)
    (e₂₁ : a₂₁ ≫ p₁ = q₂₁) (e₂₁' : p₂ ≫ b₂₁ = q₂₁)
    (e₃₂ : a₃₂ ≫ p₂ = q₃₂) (e₃₂' : p₃ ≫ b₃₂ = q₃₂)
    (e₃₁ : a₃₁ ≫ p₁ = q₃₁) (e₃₁' : p₃ ≫ b₃₁ = q₃₁)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing B₁))) :
    ((factorIso a₃₂ a₂₁ a₃₁ ha).app ((derivedPullback p₁).obj M)).symm ≪≫
      ((derivedPullback a₃₂).mapIso ((factorIso a₂₁ p₁ q₂₁ e₂₁).app M) ≪≫
        ((derivedPullback a₃₂).mapIso ((factorIso p₂ b₂₁ q₂₁ e₂₁').app M)).symm) ≪≫
      ((factorIso a₃₂ p₂ q₃₂ e₃₂).app ((derivedPullback b₂₁).obj M) ≪≫
        ((factorIso p₃ b₃₂ q₃₂ e₃₂').app ((derivedPullback b₂₁).obj M)).symm) ≪≫
      (derivedPullback p₃).mapIso ((factorIso b₃₂ b₂₁ b₃₁ hb).app M) =
    (factorIso a₃₁ p₁ q₃₁ e₃₁).app M ≪≫ ((factorIso p₃ b₃₁ q₃₁ e₃₁').app M).symm := by
  have hpb : a₃₂ ≫ q₂₁ = q₃₁ := by rw [← e₂₁, ← Category.assoc, ha, e₃₁]
  have hc : q₃₂ ≫ b₂₁ = q₃₁ := by rw [← e₃₂', Category.assoc, hb, e₃₁']
  exact paste_chase_iso ((factorIso a₃₂ a₂₁ a₃₁ ha).app _) ((factorIso a₃₁ p₁ q₃₁ e₃₁).app M)
    ((derivedPullback a₃₂).mapIso ((factorIso a₂₁ p₁ q₂₁ e₂₁).app M))
    ((factorIso a₃₂ q₂₁ q₃₁ hpb).app M)
    ((derivedPullback a₃₂).mapIso ((factorIso p₂ b₂₁ q₂₁ e₂₁').app M))
    ((factorIso a₃₂ p₂ q₃₂ e₃₂).app _) ((factorIso q₃₂ b₂₁ q₃₁ hc).app M)
    ((factorIso p₃ b₃₂ q₃₂ e₃₂').app _)
    ((derivedPullback p₃).mapIso ((factorIso b₃₂ b₂₁ b₃₁ hb).app M))
    ((factorIso p₃ b₃₁ q₃₁ e₃₁').app M)
    (factorIso_assoc a₃₂ a₂₁ p₁ q₂₁ a₃₁ q₃₁ e₂₁ ha e₃₁ hpb M)
    (factorIso_assoc a₃₂ p₂ b₂₁ q₂₁ q₃₂ q₃₁ e₂₁' e₃₂ hc hpb M)
    (factorIso_assoc p₃ b₃₂ b₂₁ b₃₁ q₃₂ q₃₁ hb e₃₂' hc e₃₁' M)

end Stacks.DerivedPullback

namespace Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] HasDerivedCategory.standard

/-- The composition isomorphism of derived pullback at the standard model is the comparison
attached to the factorisation. -/
theorem pullCompIso_eq_schemeFactorIso {A B C : AlgebraicGeometry.Scheme.{u}} (g : A ⟶ B)
    (h : B ⟶ C) (k : A ⟶ C) (w : g ≫ h = k) :
    pullCompIso g h k w = Stacks.DerivedPullback.schemeFactorIso g h k w := by
  subst w
  ext K
  simp only [pullCompIso]
  exact Category.comp_id _

end Stacks.Duality.UpperShriekDuality

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

namespace DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-! ### Two facts about a single diagonal open -/

/-- **The diagonal condition does not see automorphisms of `Δ_*𝒪_X`.** If `ξ` defines an
isomorphism `Δ_*𝒪_X ≅ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)`, so does `a ≫ ξ` for every automorphism
`a` of `Δ_*𝒪_X`: `a` is multiplication by a unit of `Γ(X, 𝒪_X)`, and the map defined by `ξ` is
`Γ(X, 𝒪_X)`-linear. -/
theorem isIso_diagonalAction_iso_comp {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K} (hξ : IsIso (D.diagonalAction K ξ))
    (a : D.diagonalObject ≅ D.diagonalObject) :
    IsIso (D.diagonalAction K (a.hom ≫ ξ)) := by
  let := D.proj.linearStructureSheafModules
  obtain ⟨s, hs⟩ := D.exists_eq_smul_id_diagonalObject a.hom
  have h : D.diagonalAction K (a.hom ≫ ξ) = a.hom ≫ D.diagonalAction K ξ :=
    calc D.diagonalAction K (a.hom ≫ ξ) = D.diagonalAction K (s • ξ) := by
          rw [hs, ← D.smul_eq_smul_id_comp s ξ]
      _ = (s • 𝟙 D.diagonalObject) ≫ D.diagonalAction K ξ := D.diagonalAction_smul s ξ
      _ = a.hom ≫ D.diagonalAction K ξ := by rw [hs]
  rw [h]
  infer_instance

/-- **No negative `Ext` from `Δ_*𝒪_X` to `L pr₁^*K|_W`** when `ξ` defines an isomorphism
`Δ_*𝒪_X ≅ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)`: by the adjunction `Δ_* ⊣ R ℰom(𝒪_X, -)` of
Stacks 0A76, `Ext^n(Δ_*𝒪_X, L pr₁^*K|_W) = Ext^n(𝒪_X, R ℰom(𝒪_X, L pr₁^*K|_W))`, and
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`. -/
theorem subsingleton_shiftedHom_diagonalObject
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K} (hξ : IsIso (D.diagonalAction K ξ))
    {n : ℤ} (hn : n < 0) :
    Subsingleton (ShiftedHom D.diagonalObject (D.derivedPullbackProj K) n) := by
  obtain ⟨e⟩ := D.nonempty_diagonalExactSupport_iso K ξ hξ
  let F := (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory
  let adj := D.diagQuotient.derivedModulePushforwardSheafHomExactSupportAdjunction
  let L := D.derivedPullbackProj K
  let O := structureSingle X
  let e₁ : (D.diagonalObject ⟶ L⟦n⟧) ≃ (F.obj O ⟶ L⟦n⟧) :=
    D.diagonalObjectIso.homCongr (Iso.refl _)
  let e₂ : (F.obj O ⟶ L⟦n⟧) ≃ ((F.obj O)⟦-n⟧ ⟶ L) :=
    ((shiftEquiv _ n).symm.toAdjunction.homEquiv _ _).symm
  let e₃ : ((F.obj O)⟦-n⟧ ⟶ L) ≃ (F.obj (O⟦-n⟧) ⟶ L) :=
    ((F.commShiftIso (-n)).app O).symm.homCongr (Iso.refl L)
  let e₄ : (F.obj (O⟦-n⟧) ⟶ L) ≃ (O⟦-n⟧ ⟶ D.diagonalExactSupport K) := adj.homEquiv _ _
  let e₅ : (O⟦-n⟧ ⟶ D.diagonalExactSupport K) ≃ (O⟦-n⟧ ⟶ O) := (Iso.refl _).homCongr e
  let e₆ : (O⟦-n⟧ ⟶ O) ≃ (O ⟶ O⟦n⟧) := (shiftEquiv _ n).symm.toAdjunction.homEquiv _ _
  exact (Equiv.subsingleton_congr (e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆)))))).2
    (Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_neg _ _ n hn)

/-- `Lg^*(L pr₁^*K|_W) ≅ L pr₁'^*(Lj^*K)|_{W'}` through the comparisons attached to the two
factorisations of `g ≫ pr₁ = pr₁' ≫ j`. -/
theorem projPullIso_eq_schemeFactorIso {X' S' : Scheme.{u}} {f' : X' ⟶ S'} (D' : DiagonalOpen f')
    (j : X' ⟶ X) (g : D'.W ⟶ D.W) (hproj : g ≫ D.proj = D'.proj ≫ j) (K : Std X) :
    D.projPullIso D' j g hproj K =
      (Stacks.DerivedPullback.schemeFactorIso g D.proj _ hproj).app K ≪≫
        ((Stacks.DerivedPullback.schemeFactorIso D'.proj j _ rfl).app K).symm := by
  simp only [projPullIso, Stacks.Duality.UpperShriekDuality.pullCompIso_eq_schemeFactorIso]
  rfl

/-- `Lg^*(L pr₁^*K|_W) ≅ L pr₁'^*(Lj^*K)|_{W'}` is natural in `K`. -/
theorem projPullIso_hom_naturality {X' S' : Scheme.{u}} {f' : X' ⟶ S'} (D' : DiagonalOpen f')
    (j : X' ⟶ X) (g : D'.W ⟶ D.W) (hproj : g ≫ D.proj = D'.proj ≫ j) {K L : Std X}
    (φ : K ⟶ L) :
    (pull g).map ((pull D.proj).map φ) ≫ (D.projPullIso D' j g hproj L).hom =
      (D.projPullIso D' j g hproj K).hom ≫ (pull D'.proj).map ((pull j).map φ) := by
  have h₁ := (Stacks.Duality.UpperShriekDuality.pullCompIso g D.proj _ hproj).hom.naturality φ
  have h₂ := (Stacks.Duality.UpperShriekDuality.pullCompIso D'.proj j _ rfl).inv.naturality φ
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [projPullIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% h₁, h₂]
  exact (Category.assoc _ _ _).symm

/-- **The comparisons `Lg^* L pr₁^* ≅ L pr₁'^* Lj^*` of two stacked squares of diagonal opens
paste** to that of the composite square, up to the composition isomorphisms of derived
pullback. -/
theorem projPullIso_paste {X₂ X₃ S₂ S₃ : Scheme.{u}} {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃}
    (D₂ : DiagonalOpen f₂) (D₃ : DiagonalOpen f₃) (j₂₁ : X₂ ⟶ X) (j₃₂ : X₃ ⟶ X₂)
    (j₃₁ : X₃ ⟶ X) (hj : j₃₂ ≫ j₂₁ = j₃₁) (g₂₁ : D₂.W ⟶ D.W) (g₃₂ : D₃.W ⟶ D₂.W)
    (g₃₁ : D₃.W ⟶ D.W) (hg : g₃₂ ≫ g₂₁ = g₃₁) (h₂₁ : g₂₁ ≫ D.proj = D₂.proj ≫ j₂₁)
    (h₃₂ : g₃₂ ≫ D₂.proj = D₃.proj ≫ j₃₂) (h₃₁ : g₃₁ ≫ D.proj = D₃.proj ≫ j₃₁) (M : Std X) :
    ((Stacks.DerivedPullback.schemeFactorIso g₃₂ g₂₁ g₃₁ hg).app ((pull D.proj).obj M)).symm ≪≫
      (pull g₃₂).mapIso (D.projPullIso D₂ j₂₁ g₂₁ h₂₁ M) ≪≫
      D₂.projPullIso D₃ j₃₂ g₃₂ h₃₂ ((pull j₂₁).obj M) ≪≫
      (pull D₃.proj).mapIso ((Stacks.DerivedPullback.schemeFactorIso j₃₂ j₂₁ j₃₁ hj).app M) =
    D.projPullIso D₃ j₃₁ g₃₁ h₃₁ M := by
  have hpb : g₃₂ ≫ D₂.proj ≫ j₂₁ = D₃.proj ≫ j₃₁ := by
    rw [← Category.assoc, h₃₂, Category.assoc, hj]
  have hc : (D₃.proj ≫ j₃₂) ≫ j₂₁ = D₃.proj ≫ j₃₁ := by rw [Category.assoc, hj]
  let c := fun {A B : Scheme.{u}} (m : A ⟶ B) => m.toLRSHom.toShHom
  exact Stacks.DerivedPullback.paste_chase_fun (pull g₃₂) (pull D₃.proj)
    ((Stacks.DerivedPullback.schemeFactorIso g₂₁ D.proj _ h₂₁).app M)
    ((Stacks.DerivedPullback.schemeFactorIso D₂.proj j₂₁ _ rfl).app M)
    (D.projPullIso D₂ j₂₁ g₂₁ h₂₁ M) (D.projPullIso_eq_schemeFactorIso D₂ j₂₁ g₂₁ h₂₁ M)
    ((Stacks.DerivedPullback.schemeFactorIso j₃₂ j₂₁ j₃₁ hj).app M)
    ((Stacks.DerivedPullback.schemeFactorIso g₃₂ g₂₁ g₃₁ hg).app ((pull D.proj).obj M))
    ((Stacks.DerivedPullback.schemeFactorIso g₃₁ D.proj _ h₃₁).app M)
    ((Stacks.DerivedPullback.schemeFactorIso g₃₂ (D₂.proj ≫ j₂₁) _ hpb).app M)
    ((Stacks.DerivedPullback.schemeFactorIso g₃₂ D₂.proj _ h₃₂).app ((pull j₂₁).obj M))
    ((Stacks.DerivedPullback.schemeFactorIso (D₃.proj ≫ j₃₂) j₂₁ _ hc).app M)
    ((Stacks.DerivedPullback.schemeFactorIso D₃.proj j₃₂ _ rfl).app ((pull j₂₁).obj M))
    ((Stacks.DerivedPullback.schemeFactorIso D₃.proj j₃₁ _ rfl).app M)
    (D₂.projPullIso D₃ j₃₂ g₃₂ h₃₂ ((pull j₂₁).obj M))
    (D₂.projPullIso_eq_schemeFactorIso D₃ j₃₂ g₃₂ h₃₂ ((pull j₂₁).obj M))
    (D.projPullIso D₃ j₃₁ g₃₁ h₃₁ M) (D.projPullIso_eq_schemeFactorIso D₃ j₃₁ g₃₁ h₃₁ M)
    (Stacks.DerivedPullback.factorIso_assoc (c g₃₂) (c g₂₁) (c D.proj) (c (D₂.proj ≫ j₂₁))
      (c g₃₁) (c (D₃.proj ≫ j₃₁)) (congrArg c h₂₁) (congrArg c hg) (congrArg c h₃₁)
      (congrArg c hpb) M)
    (Stacks.DerivedPullback.factorIso_assoc (c g₃₂) (c D₂.proj) (c j₂₁) (c (D₂.proj ≫ j₂₁))
      (c (D₃.proj ≫ j₃₂)) (c (D₃.proj ≫ j₃₁)) rfl (congrArg c h₃₂) (congrArg c hc)
      (congrArg c hpb) M)
    (Stacks.DerivedPullback.factorIso_assoc (c D₃.proj) (c j₃₂) (c j₂₁) (c j₃₁)
      (c (D₃.proj ≫ j₃₂)) (c (D₃.proj ≫ j₃₁)) (congrArg c hj) rfl (congrArg c hc) rfl M)

/-! ### Restricting to the charts `W ∩ (U ×_S U)` and transporting between them -/

open Scheme.DerivedPullbackOpensGlueing (resComp pullbackLE pullbackLEComp)

/-- `Lι^*(Δ_*𝒪_X) ≅ Δ_{U*}𝒪_U` on `W ∩ (U ×_S U)`, at the base change square of `Δ`. -/
def squareDiagonalIso (U : X.Opens) :
    (pull (D.squareOpens U).ι).obj D.diagonalObject ≅ (D.opensRestrict U).diagonalObject :=
  D.diagonalObjectPullIso (D.opensRestrict U) (D.squareOpens U).ι U.ι
    (D.isPullback_opensRestrictDiag U)

/-- `Lι^*(L pr₁^*K|_W) ≅ L pr₁^*(K|_U)|_{W ∩ (U ×_S U)}`. -/
def squareProjIso (U : X.Opens) (M : Std X) :
    (pull (D.squareOpens U).ι).obj ((pull D.proj).obj M) ≅
      (pull (D.opensRestrict U).proj).obj ((pull U.ι).obj M) :=
  D.projPullIso (D.opensRestrict U) U.ι (D.squareOpens U).ι (D.opensRestrict_proj_ι U).symm M

/-- For `V ⊆ U`, the identification of the two diagonal objects on `W ∩ (V ×_S V)` obtained by
restricting from `W` in one or in two steps. -/
def transitionDiagonalIso {U V : X.Opens} (h : V ≤ U) :
    (pull (D.W.homOfLE (squareOpens_mono h))).obj (D.opensRestrict U).diagonalObject ≅
      (D.opensRestrict V).diagonalObject :=
  (pull (D.W.homOfLE (squareOpens_mono h))).mapIso (D.squareDiagonalIso U).symm ≪≫
    resComp (X := D.W) (squareOpens_mono h) D.diagonalObject ≪≫ D.squareDiagonalIso V

/-- For `V ⊆ U`, `L(W_V ⊆ W_U)^* L pr₁^*M ≅ L pr₁^*(M|_V)`. -/
def transitionProjIso {U V : X.Opens} (h : V ≤ U) (M : Std U) :
    (pull (D.W.homOfLE (squareOpens_mono h))).obj ((pull (D.opensRestrict U).proj).obj M) ≅
      (pull (D.opensRestrict V).proj).obj ((pull (X.homOfLE h)).obj M) :=
  (D.opensRestrict U).projPullIso (D.opensRestrict V) (X.homOfLE h)
    (D.W.homOfLE (squareOpens_mono h)) (D.homOfLE_opensRestrict_proj h) M

/-- **Transport between charts**: for `V ⊆ U` and `ζ : Δ_{U*}𝒪_U ⟶ L pr₁^*M`, the map
`Δ_{V*}𝒪_V ⟶ L pr₁^*(M|_V)` it induces on `W ∩ (V ×_S V)`. -/
def squareTransport {U V : X.Opens} (h : V ≤ U) {M : Std U}
    (ζ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj M) :
    ((D.opensRestrict V).diagonalObject : Std (D.opensRestrict V).W) ⟶
      (pull (D.opensRestrict V).proj).obj ((pull (X.homOfLE h)).obj M) :=
  (D.transitionDiagonalIso h).inv ≫ (pull (D.W.homOfLE (squareOpens_mono h))).map ζ ≫
    (D.transitionProjIso h M).hom

/-- Transport between charts is natural in `M`. -/
theorem squareTransport_comp {U V : X.Opens} (h : V ≤ U) {M N : Std U}
    (ζ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj M) (φ : M ⟶ N) :
    D.squareTransport h (ζ ≫ (pull (D.opensRestrict U).proj).map φ) =
      D.squareTransport h ζ ≫ (pull (D.opensRestrict V).proj).map ((pull (X.homOfLE h)).map φ) := by
  have hn : (pull (D.W.homOfLE (squareOpens_mono h))).map ((pull (D.opensRestrict U).proj).map φ) ≫
      (D.transitionProjIso h N).hom = (D.transitionProjIso h M).hom ≫
        (pull (D.opensRestrict V).proj).map ((pull (X.homOfLE h)).map φ) :=
    (D.opensRestrict U).projPullIso_hom_naturality (D.opensRestrict V) (X.homOfLE h)
      (D.W.homOfLE (squareOpens_mono h)) (D.homOfLE_opensRestrict_proj h) φ
  exact Stacks.DerivedPullback.conj_map_comp _ _ _ _ _ _ _ hn

/-- **Transporting twice between charts is transporting once**, up to the composition
isomorphism of the restrictions `W ⊆ V ⊆ U`. -/
theorem squareTransport_squareTransport {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) {M : Std U}
    (ζ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj M) :
    D.squareTransport h₂ (D.squareTransport h₁ ζ) ≫
        (pull (D.opensRestrict W).proj).map (pullbackLEComp h₂ h₁ M).hom =
      D.squareTransport (h₂.trans h₁) ζ := by
  let g₁ := D.W.homOfLE (squareOpens_mono h₁)
  let g₂ := D.W.homOfLE (squareOpens_mono h₂)
  let g₃ := D.W.homOfLE (squareOpens_mono (h₂.trans h₁))
  have hg : g₂ ≫ g₁ = g₃ := D.W.homOfLE_homOfLE _ _
  have hj : X.homOfLE h₂ ≫ X.homOfLE h₁ = X.homOfLE (h₂.trans h₁) := X.homOfLE_homOfLE _ _
  exact Stacks.DerivedPullback.transport_comp_chase (pull g₁) (pull g₂) (pull g₃)
    (Stacks.DerivedPullback.schemeFactorIso g₂ g₁ g₃ hg) (pull (D.opensRestrict W).proj)
    (D.squareDiagonalIso U) (D.squareDiagonalIso V) (D.squareDiagonalIso W)
    (resComp (X := D.W) (squareOpens_mono h₁) D.diagonalObject)
    (resComp (X := D.W) (squareOpens_mono h₂) D.diagonalObject)
    (resComp (X := D.W) (squareOpens_mono (h₂.trans h₁)) D.diagonalObject)
    (pullbackLEComp (X := D.W) (squareOpens_mono h₂) (squareOpens_mono h₁)
      ((pull (D.squareOpens U).ι).obj D.diagonalObject))
    (Scheme.DerivedPullbackOpensGlueing.derivedPullbackCompObj_trans_congrObj _ _ _ _ _)
    (Scheme.DerivedPullbackOpensGlueing.pullbackLEComp_hom_resComp_hom (X := D.W)
      (squareOpens_mono h₂) (squareOpens_mono h₁) D.diagonalObject)
    (D.transitionProjIso h₁ M) (D.transitionProjIso h₂ ((pull (X.homOfLE h₁)).obj M))
    (D.transitionProjIso (h₂.trans h₁) M) (pullbackLEComp h₂ h₁ M)
    ((Stacks.DerivedPullback.schemeFactorIso (X.homOfLE h₂) (X.homOfLE h₁)
      (X.homOfLE (h₂.trans h₁)) hj).app M)
    (Scheme.DerivedPullbackOpensGlueing.derivedPullbackCompObj_trans_congrObj _ _ _ _ _)
    ((D.opensRestrict U).projPullIso_paste (D.opensRestrict V) (D.opensRestrict W)
      (X.homOfLE h₁) (X.homOfLE h₂) (X.homOfLE (h₂.trans h₁)) hj g₁ g₂ g₃ hg
      (D.homOfLE_opensRestrict_proj h₁) (D.homOfLE_opensRestrict_proj h₂)
      (D.homOfLE_opensRestrict_proj (h₂.trans h₁)) M) ζ

/-- **Restricting a morphism on `W ∩ (U ×_S U)` to `W ∩ (V ×_S V)` is transporting it between
the charts**, read through the identifications with `Δ_{U*}𝒪_U` and `L pr₁^*(K|_U)`. -/
theorem squareTransport_restrict {U V : X.Opens} (h : V ≤ U) (K : Std X)
    (α : (pull (D.squareOpens U).ι).obj D.diagonalObject ⟶
      (pull (D.squareOpens U).ι).obj ((pull D.proj).obj K)) :
    D.squareTransport h ((D.squareDiagonalIso U).inv ≫ α ≫ (D.squareProjIso U K).hom) ≫
        (pull (D.opensRestrict V).proj).map (resComp h K).hom =
      (D.squareDiagonalIso V).inv ≫
        ((resComp (X := D.W) (squareOpens_mono h) D.diagonalObject).inv ≫
          (pull (D.W.homOfLE (squareOpens_mono h))).map α ≫
          (resComp (X := D.W) (squareOpens_mono h) ((pull D.proj).obj K)).hom) ≫
        (D.squareProjIso V K).hom := by
  let g := D.W.homOfLE (squareOpens_mono h)
  have hg : g ≫ (D.squareOpens U).ι = (D.squareOpens V).ι := D.W.homOfLE_ι _
  have hj : X.homOfLE h ≫ U.ι = V.ι := X.homOfLE_ι _
  exact Stacks.DerivedPullback.restrict_transport_chase (pull g) (D.squareDiagonalIso U)
    (D.squareDiagonalIso V) (resComp (X := D.W) (squareOpens_mono h) D.diagonalObject)
    (resComp (X := D.W) (squareOpens_mono h) ((pull D.proj).obj K))
    ((Stacks.DerivedPullback.schemeFactorIso g (D.squareOpens U).ι (D.squareOpens V).ι hg).app
      ((pull D.proj).obj K))
    (Scheme.DerivedPullbackOpensGlueing.derivedPullbackCompObj_trans_congrObj _ _ _ _ _)
    (D.squareProjIso U K) (D.squareProjIso V K) (D.transitionProjIso h ((pull U.ι).obj K))
    ((pull (D.opensRestrict V).proj).mapIso (resComp h K))
    ((pull (D.opensRestrict V).proj).mapIso
      ((Stacks.DerivedPullback.schemeFactorIso (X.homOfLE h) U.ι V.ι hj).app K))
    (congrArg (pull (D.opensRestrict V).proj).mapIso
      (Scheme.DerivedPullbackOpensGlueing.derivedPullbackCompObj_trans_congrObj _ _ _ _ _))
    (D.projPullIso_paste (D.opensRestrict U) (D.opensRestrict V) U.ι (X.homOfLE h) V.ι hj
      (D.squareOpens U).ι g (D.squareOpens V).ι hg (D.opensRestrict_proj_ι U).symm
      (D.homOfLE_opensRestrict_proj h) (D.opensRestrict_proj_ι V).symm K) α

/-! ### Glueing morphisms on `W` from the charts `W ∩ (U ×_S U)` -/

/-- The covering of `W` used to glue morphisms out of `Δ_*𝒪_X`: the opens missing `Δ(X)`, and the
charts `W ∩ (U ×_S U)` for `U` an affine open of `X` lying over an affine open of `S`. -/
def chartCover : Set D.W.Opens :=
  {P | (∀ x : X, D.diag.base x ∉ P) ∨ ∃ U, U ∈ chartOpens f ∧ D.squareOpens U = P}

/-- The complement of `Δ(X)` in `W`. -/
def offDiagonal : D.W.Opens :=
  haveI := D.isClosedImmersion
  ⟨(Set.range D.diag.base)ᶜ, D.diag.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- No point of the diagonal `Δ(X)` lies in the complement `offDiagonal` of `Δ(X)` in `W`. -/
theorem not_mem_offDiagonal (x : X) : D.diag.base x ∉ D.offDiagonal := fun h => h ⟨x, rfl⟩

/-- Every point of `W` lies in a member of the covering inside a given intersection of
members. -/
theorem exists_mem_chartCover {P Q : D.W.Opens} (hP : P ∈ D.chartCover) (hQ : Q ∈ D.chartCover)
    {w : D.W} (hw : w ∈ P ⊓ Q) : ∃ R ∈ D.chartCover, R ≤ P ⊓ Q ∧ w ∈ R := by
  by_cases hr : w ∈ Set.range D.diag.base
  · obtain ⟨y, rfl⟩ := hr
    obtain ⟨U, hU, rfl⟩ := hP.resolve_left fun h => h y hw.1
    obtain ⟨U', hU', rfl⟩ := hQ.resolve_left fun h => h y hw.2
    have hy : y ∈ U ⊓ U' := ⟨(D.diag_mem_squareOpens_iff y).1 hw.1,
      (D.diag_mem_squareOpens_iff y).1 hw.2⟩
    obtain ⟨U'', hU'', hyU'', hle⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_chartOpens f) hy
    exact ⟨D.squareOpens U'', Or.inr ⟨U'', hU'', rfl⟩,
      le_inf (squareOpens_mono (hle.trans inf_le_left)) (squareOpens_mono (hle.trans inf_le_right)),
      (D.diag_mem_squareOpens_iff y).2 hyU''⟩
  · exact ⟨P ⊓ Q ⊓ D.offDiagonal, Or.inl fun x hx => D.not_mem_offDiagonal x hx.2, inf_le_left,
      ⟨hw, hr⟩⟩

/-- Every point of `X` lies in a chart. -/
private theorem exists_mem_chartOpens (x : X) : ∃ U ∈ chartOpens f, x ∈ U :=
  let ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_chartOpens f)
    (show x ∈ (⊤ : X.Opens) from trivial)
  ⟨U, hU, hxU⟩

/-- The opens of `chartCover` cover `W`. -/
theorem sSup_chartCover : sSup D.chartCover = ⊤ := by
  refine top_le_iff.mp fun w _ => Opens.mem_sSup.mpr ?_
  by_cases hr : w ∈ Set.range D.diag.base
  · obtain ⟨y, rfl⟩ := hr
    obtain ⟨U, hU, hyU⟩ := exists_mem_chartOpens (f := f) y
    exact ⟨D.squareOpens U, Or.inr ⟨U, hU, rfl⟩, (D.diag_mem_squareOpens_iff y).2 hyU⟩
  · exact ⟨D.offDiagonal, Or.inl D.not_mem_offDiagonal, hr⟩

/-- The intersection of two members of `chartCover` is the union of the members of `chartCover`
contained in it. -/
theorem chartCover_inf_eq {P Q : D.W.Opens} (hP : P ∈ D.chartCover) (hQ : Q ∈ D.chartCover) :
    P ⊓ Q = sSup {R | R ∈ D.chartCover ∧ R ≤ P ⊓ Q} := by
  refine le_antisymm (fun w hw => Opens.mem_sSup.mpr ?_) (sSup_le fun R hR => hR.2)
  obtain ⟨R, hR, hle, hwR⟩ := D.exists_mem_chartCover hP hQ hw
  exact ⟨R, ⟨hR, hle⟩, hwR⟩

/-- **Glueing morphisms on `W` from the charts.** Let `A, L ∈ D(𝒪_W)` with `A` vanishing on
every open of `W` missing `Δ(X)`. A family of morphisms `A|_{W_U} ⟶ L|_{W_U}` on the charts
`W_U = W ∩ (U ×_S U)`, compatible with restriction along `W_V ⊆ W_U` and with no negative `Ext`
on the charts, comes from a morphism `A ⟶ L` (Stacks 0D66 on the covering of `W` by the charts and
the opens missing `Δ(X)`). -/
theorem exists_hom_of_squareOpens {A L : DerivedCategory D.W.Modules}
    (hA : ∀ P : D.W.Opens, (∀ x : X, D.diag.base x ∉ P) →
      IsZero ((derivedPullback P.ι.toLRSHom.toShHom).obj A))
    (φ' : ∀ U ∈ chartOpens f, (derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).obj A ⟶
      (derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).obj L)
    (hφ' : ∀ (U : X.Opens) (hU : U ∈ chartOpens f) (V : X.Opens) (hV : V ∈ chartOpens f)
      (h : V ≤ U), (resComp (squareOpens_mono (D := D) h) A).inv ≫
        (pullbackLE (squareOpens_mono (D := D) h)).map (φ' U hU) ≫
          (resComp (squareOpens_mono (D := D) h) L).hom = φ' V hV)
    (hExt : ∀ U ∈ chartOpens f, ∀ n : ℤ, n < 0 → Subsingleton (ShiftedHom
      ((derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).obj A)
      ((derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).obj L) n)) :
    ∃ ψ : A ⟶ L, ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      (derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).map ψ = φ' U hU := by
  classical
  let φc : ∀ (P : D.W.Opens) (U : X.Opens), U ∈ chartOpens f → D.squareOpens U = P →
      ((derivedPullback P.ι.toLRSHom.toShHom).obj A ⟶
        (derivedPullback P.ι.toLRSHom.toShHom).obj L) :=
    fun P U hU h => h ▸ φ' U hU
  have hφc : ∀ (P : D.W.Opens) (U₁ U₂ : X.Opens) (h₁ : U₁ ∈ chartOpens f)
      (h₂ : U₂ ∈ chartOpens f) (e₁ : D.squareOpens U₁ = P) (e₂ : D.squareOpens U₂ = P),
      U₁ = U₂ → φc P U₁ h₁ e₁ = φc P U₂ h₂ e₂ := by
    rintro P U₁ _ _ _ _ _ rfl
    rfl
  let φ : ∀ P ∈ D.chartCover, (derivedPullback P.ι.toLRSHom.toShHom).obj A ⟶
      (derivedPullback P.ι.toLRSHom.toShHom).obj L := fun P hP =>
    if hd : ∀ x : X, D.diag.base x ∉ P then 0 else
      φc P (Classical.choose (hP.resolve_left hd)) (Classical.choose_spec (hP.resolve_left hd)).1
        (Classical.choose_spec (hP.resolve_left hd)).2
  have hφ : ∀ (P : D.W.Opens) (hP : P ∈ D.chartCover) (U : X.Opens) (hU : U ∈ chartOpens f)
      (hPU : D.squareOpens U = P), φ P hP = φc P U hU hPU := by
    intro P hP U hU hPU
    by_cases hd : ∀ x : X, D.diag.base x ∉ P
    · exact (hA P hd).eq_of_src _ _
    · refine (dif_neg hd).trans (hφc P _ U _ hU _ hPU ?_)
      have hc := Classical.choose_spec (hP.resolve_left hd)
      exact le_antisymm (le_of_squareOpens_le (hc.2.trans hPU.symm).le)
        (le_of_squareOpens_le (hPU.trans hc.2.symm).le)
  obtain ⟨ψ, hψ, -⟩ := Scheme.DerivedPullbackOpensGlueing.existsUnique_hom_of_derivedPullback_opens
    D.chartCover D.sSup_chartCover (fun P hP Q hQ => D.chartCover_inf_eq hP hQ)
    (fun P hP n hn => by
      by_cases hd : ∀ x : X, D.diag.base x ∉ P
      · exact ⟨fun a b => (hA P hd).eq_of_src a b⟩
      · obtain ⟨U, hU, rfl⟩ := hP.resolve_left hd
        exact hExt U hU n hn) φ
    (fun P hP P' hP' hle => by
      by_cases hd' : ∀ x : X, D.diag.base x ∉ P'
      · exact (hA P' hd').eq_of_src _ _
      · have hd : ¬ ∀ x : X, D.diag.base x ∉ P := fun h => hd' fun x hx => h x (hle hx)
        obtain ⟨U, hU, rfl⟩ := hP.resolve_left hd
        obtain ⟨U', hU', rfl⟩ := hP'.resolve_left hd'
        rw [hφ _ hP U hU rfl, hφ _ hP' U' hU' rfl]
        exact hφ' U hU U' hU' (le_of_squareOpens_le hle))
  exact ⟨ψ, fun U hU => (hψ _ (Or.inr ⟨U, hU, rfl⟩)).trans (hφ _ (Or.inr ⟨U, hU, rfl⟩) U hU rfl)⟩

end DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  (D : DiagonalOpen f)

/-- **Transport between charts preserves relative dualizing complexes.** -/
theorem IsRelativeDualizingComplex.squareTransport {U V : X.Opens} (h : V ≤ U) {M : Std U}
    {ζ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj M}
    (hM : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U) M ζ) :
    IsRelativeDualizingComplex (V.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (V.ι ≫ f).base)) (D.opensRestrict V)
      ((pull (X.homOfLE h)).obj M) (D.squareTransport h ζ) := by
  let g := D.W.homOfLE (DiagonalOpen.squareOpens_mono (D := D) h)
  let eΔ := (D.opensRestrict U).diagonalObjectPullIso (D.opensRestrict V) g (X.homOfLE h)
    (D.isPullback_opensRestrictDiag_homOfLE h)
  have h₀ := hM.transport_of (D.opensRestrict V) (X.homOfLE h) (Scheme.homOfLE_ι_assoc _ _ _) g
    (D.homOfLE_opensRestrict_proj h) eΔ
    ((D.opensRestrict U).diagonalObjectPullIso_mul (D.opensRestrict V) g (X.homOfLE h)
      (D.isPullback_opensRestrictDiag_homOfLE h))
  have e : D.squareTransport h ζ = ((D.transitionDiagonalIso h).symm ≪≫ eΔ).hom ≫
      (eΔ.inv ≫ (pull g).map ζ ≫ (D.transitionProjIso h M).hom) :=
    Stacks.DerivedPullback.trans_symm_hom_comp _ _ _
  constructor
  · exact h₀.isPerfectRelativeTo
  · have h₂ := (D.opensRestrict V).isIso_diagonalAction_iso_comp h₀.isIso_diagonalAction
      ((D.transitionDiagonalIso h).symm ≪≫ eΔ)
    rw [e]
    exact h₂

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- An affine open lying over an affine open of `S` is a chart of itself: `⊤` is an affine open
of `V` mapping into an affine open of `S`. -/
theorem top_mem_chartOpens_comp {V : X.Opens} (hV : V ∈ chartOpens f) :
    (⊤ : V.toScheme.Opens) ∈ chartOpens (V.ι ≫ f) := by
  obtain ⟨hVa, V', hV', hVV'⟩ := hV
  have : IsAffine V.toScheme := hVa
  refine ⟨isAffineOpen_top V.toScheme, V', hV', ?_⟩
  rw [Scheme.Hom.comp_preimage, ← Scheme.Opens.ι_preimage_self V]
  exact V.ι.preimage_mono hVV'

/-- **Two relative dualizing complexes on a chart are isomorphic**: for `V` an affine open lying
over an affine open of `S`, any two relative dualizing complexes for `V ⟶ S` have isomorphic
underlying objects (Stacks 0E2U and Stacks 0E2D, through `⊤ ⊆ V`). -/
theorem IsRelativeDualizingComplex.nonempty_iso_of_mem_chartOpens {V : X.Opens}
    (hV : V ∈ chartOpens f) {D' : DiagonalOpen (V.ι ≫ f)} {K L : DerivedCategory V.toScheme.Modules}
    {ξ : D'.diagonalObject ⟶ D'.derivedPullbackProj K}
    {η : D'.diagonalObject ⟶ D'.derivedPullbackProj L}
    (hK : IsRelativeDualizingComplex (V.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (V.ι ≫ f).base)) D' K ξ)
    (hL : IsRelativeDualizingComplex (V.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (V.ι ≫ f).base)) D' L η) :
    Nonempty (K ≅ L) :=
  let ⟨e⟩ := hK.nonempty_iso_restrict_of_mem_chartOpens hL (top_mem_chartOpens_comp hV)
  ⟨(Scheme.DerivedPullbackOpensGlueing.topFullyFaithful V.toScheme).preimageIso e⟩

/-- **A relative dualizing complex has no negative self-`Ext`**, as an object of `D(𝒪_X)` itself:
the case `W = ⊤` of `subsingleton_shiftedHom_preimageRestrict`, through the faithfulness of
restriction to `⊤`. -/
theorem IsRelativeDualizingComplex.subsingleton_shiftedHom_self {D : DiagonalOpen f}
    {K : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ) {n : ℤ} (hn : n < 0) :
    Subsingleton (ShiftedHom K K n) := by
  let O := structureSheafRing X.toRingedSpace
  exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_overTop O K K n
    (hK.subsingleton_shiftedHom_preimageRestrict ⊤ hn)

/-- **The transition isomorphisms between the charts** (proof of Stacks 0E2X): for `V ⊆ U` charts
and relative dualizing complexes `(K_U, ξ_U)`, `(K_V, ξ_V)` on `W ∩ (U ×_S U)` and
`W ∩ (V ×_S V)`, there is a unique isomorphism `K_U|_V ≅ K_V` carrying the transport of `ξ_U` to
`ξ_V` (Stacks 0E2W on `V`). -/
theorem existsUnique_transition_iso {U V : X.Opens} (hV : V ∈ chartOpens f) (h : V ≤ U)
    {KU : Std U} {ξU : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU}
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U) KU ξU)
    {KV : Std V} {ξV : ((D.opensRestrict V).diagonalObject : Std (D.opensRestrict V).W) ⟶
      (pull (D.opensRestrict V).proj).obj KV}
    (hKV : IsRelativeDualizingComplex (V.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (V.ι ≫ f).base)) (D.opensRestrict V) KV ξV) :
    ∃! ρ : (pull (X.homOfLE h)).obj KU ≅ KV,
      D.squareTransport h ξU ≫ (pull (D.opensRestrict V).proj).map ρ.hom = ξV := by
  have hT := hKU.squareTransport D h
  obtain ⟨α⟩ := hT.nonempty_iso_of_mem_chartOpens hV hKV
  obtain ⟨β, hβ⟩ := IsRelativeDualizingComplex.exists_iso_comp_eq_of_isIso
    hT.isIso_diagonalAction hKV.isIso_diagonalAction α
  exact ⟨β, hβ, fun γ hγ => IsRelativeDualizingComplex.iso_ext_of_comp_eq hT hγ hβ⟩

open Scheme.DerivedPullbackOpensGlueing (resComp pullbackLE pullbackLEComp) in
/-- **Glueing the chart complexes** (proof of Stacks 0E2X, BBD step): given relative dualizing
complexes `(K_U, ξ_U)` on the charts `W ∩ (U ×_S U)`, `U ∈ ℬ`, there are `K ∈ D(𝒪_X)` and
isomorphisms `σ_U : K|_U ≅ K_U` such that, for `V ⊆ U` in `ℬ`, the isomorphism
`K_U|_V ≅ K|_V ≅ K_V` they induce carries the transport of `ξ_U` to `ξ_V`. -/
theorem exists_glueing_chart
    (KU : ∀ U ∈ chartOpens f, Std U)
    (ξU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
        (pull (D.opensRestrict U).proj).obj (KU U hU))
    (hKU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U)
        (KU U hU) (ξU U hU)) :
    ∃ (K : Std X) (σ : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), (pull U.ι).obj K ≅ KU U hU),
      ∀ (V U : X.Opens) (h : V ≤ U) (hU : U ∈ chartOpens f) (hV : V ∈ chartOpens f),
        D.squareTransport h (ξU U hU) ≫ (pull (D.opensRestrict V).proj).map
          ((pull (X.homOfLE h)).map (σ U hU).inv ≫ (resComp h K).hom ≫ (σ V hV).hom) =
          ξU V hV := by
  choose ρ hρ using fun (V U : X.Opens) (h : V ≤ U) (hU : U ∈ chartOpens f)
    (hV : V ∈ chartOpens f) =>
      (existsUnique_transition_iso D hV h (hKU U hU) (hKU V hV)).exists
  have hcocycle : ∀ (W V U : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (hU : U ∈ chartOpens f)
      (hV : V ∈ chartOpens f) (hW : W ∈ chartOpens f),
      (ρ W U (hWV.trans hVU) hU hW).hom = (pullbackLEComp hWV hVU (KU U hU)).inv ≫
        (pullbackLE hWV).map (ρ V U hVU hU hV).hom ≫ (ρ W V hWV hV hW).hom := by
    intro W V U hWV hVU hU hV hW
    let R : (pull (X.homOfLE (hWV.trans hVU))).obj (KU U hU) ≅ KU W hW :=
      (pullbackLEComp hWV hVU (KU U hU)).symm ≪≫ (pullbackLE hWV).mapIso (ρ V U hVU hU hV) ≪≫
        ρ W V hWV hV hW
    have hR : D.squareTransport (hWV.trans hVU) (ξU U hU) ≫
        (pull (D.opensRestrict W).proj).map R.hom = ξU W hW :=
      Stacks.DerivedPullback.cocycle_chase (pull (D.opensRestrict W).proj)
        (D.squareTransport hWV (D.squareTransport hVU (ξU U hU)))
        (D.squareTransport (hWV.trans hVU) (ξU U hU)) (D.squareTransport hWV (ξU V hV))
        (ξU W hW) (pullbackLEComp hWV hVU (KU U hU)) ((pullbackLE hWV).map (ρ V U hVU hU hV).hom)
        (ρ W V hWV hV hW).hom (D.squareTransport_squareTransport hVU hWV (ξU U hU))
        ((D.squareTransport_comp hWV (D.squareTransport hVU (ξU U hU))
          (ρ V U hVU hU hV).hom).symm.trans
            (congrArg (D.squareTransport hWV) (hρ V U hVU hU hV)))
        (hρ W V hWV hV hW)
    exact congrArg Iso.hom ((existsUnique_transition_iso D hW (hWV.trans hVU) (hKU U hU)
      (hKU W hW)).unique (hρ W U (hWV.trans hVU) hU hW) hR)
  obtain ⟨K, σ, hσ⟩ := Scheme.DerivedPullbackOpensGlueing.exists_glueing_of_derivedPullback_opens
    (chartOpens f) KU ρ (sSup_chartOpens f) (fun U _ V _ => eq_sSup_chartOpens f (U ⊓ V))
    hcocycle (fun U hU n hn => (hKU U hU).subsingleton_shiftedHom_self hn)
  exact ⟨K, σ, fun V U h hU hV => (congrArg (fun m => D.squareTransport h (ξU U hU) ≫
    (pull (D.opensRestrict V).proj).map m)
      (Stacks.DerivedPullback.glueing_chase (pullbackLE h) (resComp h K) (σ U hU) (σ V hV)
        (ρ V U h hU hV) (hσ V U h hU hV))).trans (hρ V U h hU hV)⟩

namespace DiagonalOpen

open Scheme.DerivedPullbackOpensGlueing (resComp pullbackLE)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `Δ_*𝒪_X` vanishes on every open of `W` missing `Δ(X)`. -/
theorem isZero_pull_diagonalObject (P : D.W.Opens) (hP : ∀ x : X, D.diag.base x ∉ P) :
    IsZero ((pull P.ι).obj D.diagonalObject) :=
  IsZero.of_iso (D.isZero_derivedPullback_pushforward P.ι
    (fun z hz => by
      obtain ⟨x, hx⟩ := hz
      have hz' : P.ι.base z ∈ P := by
        have := Set.mem_range_self (f := P.ι.base) z
        rwa [Scheme.Opens.range_ι] at this
      exact hP x (by rwa [hx]))
    (structureSingle X)) ((pull P.ι).mapIso D.diagonalObjectIso)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The chart map** `Δ_*𝒪_X|_{W_U} ⟶ L pr₁^*K|_{W_U}` on `W_U = W ∩ (U ×_S U)` defined by a map
`ξ_U : Δ_{U*}𝒪_U ⟶ L pr₁^*K_U` and an identification `σ : K|_U ≅ K_U`. -/
def chartHom (U : X.Opens) (K : Std X) {KU : Std U}
    (ξ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU) (σ : (pull U.ι).obj K ≅ KU) :
    (pull (D.squareOpens U).ι).obj D.diagonalObject ⟶
      (pull (D.squareOpens U).ι).obj ((pull D.proj).obj K) :=
  (D.squareDiagonalIso U).hom ≫ ξ ≫ (pull (D.opensRestrict U).proj).map σ.inv ≫
    (D.squareProjIso U K).inv

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- Conjugating `chartHom U K ξ σ` by `squareDiagonalIso U` and `squareProjIso U K` recovers
`ξ` followed by the map induced by `σ⁻¹`. -/
theorem chartHom_cancel (U : X.Opens) (K : Std X) {KU : Std U}
    (ξ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU) (σ : (pull U.ι).obj K ≅ KU) :
    (D.squareDiagonalIso U).inv ≫ D.chartHom U K ξ σ ≫ (D.squareProjIso U K).hom =
      ξ ≫ (pull (D.opensRestrict U).proj).map σ.inv :=
  Stacks.DerivedPullback.conj_cancel_chase (D.squareDiagonalIso U) (D.squareProjIso U K) ξ
    ((pull (D.opensRestrict U).proj).map σ.inv)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **The chart maps are compatible with shrinking the chart**, when the identifications `σ`
carry the transported `ξ_U` to `ξ_V`. -/
theorem chartHom_restrict {U V : X.Opens} (h : V ≤ U) (K : Std X) {KU : Std U} {KV : Std V}
    (ξU : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU)
    (ξV : ((D.opensRestrict V).diagonalObject : Std (D.opensRestrict V).W) ⟶
      (pull (D.opensRestrict V).proj).obj KV)
    (σU : (pull U.ι).obj K ≅ KU) (σV : (pull V.ι).obj K ≅ KV)
    (hσ : D.squareTransport h ξU ≫ (pull (D.opensRestrict V).proj).map
      ((pull (X.homOfLE h)).map σU.inv ≫ (resComp h K).hom ≫ σV.hom) = ξV) :
    (resComp (squareOpens_mono (D := D) h) D.diagonalObject).inv ≫
        (pullbackLE (squareOpens_mono (D := D) h)).map (D.chartHom U K ξU σU) ≫
          (resComp (squareOpens_mono (D := D) h) ((pull D.proj).obj K)).hom =
      D.chartHom V K ξV σV :=
  Stacks.DerivedPullback.chart_compat_chase (pull (D.opensRestrict V).proj)
    (D.squareDiagonalIso V) (D.squareProjIso V K) _
    (D.squareTransport h ((D.squareDiagonalIso U).inv ≫ D.chartHom U K ξU σU ≫
      (D.squareProjIso U K).hom))
    (D.squareTransport h ξU) ((pull (X.homOfLE h)).map σU.inv)
    ((congrArg (D.squareTransport h) (D.chartHom_cancel U K ξU σU)).trans
      (D.squareTransport_comp h ξU σU.inv))
    (resComp h K).hom (D.squareTransport_restrict h K (D.chartHom U K ξU σU)) σV ξV hσ

end DiagonalOpen

/-- No negative `Ext` between the restrictions of `Δ_*𝒪_X` and of `L pr₁^*K|_W` to a chart on
which `K` restricts to a relative dualizing complex. -/
theorem IsRelativeDualizingComplex.subsingleton_shiftedHom_squareOpens (U : X.Opens) (K : Std X)
    {KU : Std U} {ξ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU}
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U) KU ξ)
    (σ : (pull U.ι).obj K ≅ KU) {n : ℤ} (hn : n < 0) :
    Subsingleton (ShiftedHom ((pull (D.squareOpens U).ι).obj D.diagonalObject)
      ((pull (D.squareOpens U).ι).obj ((pull D.proj).obj K)) n) :=
  Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso (D.squareDiagonalIso U)
    (D.squareProjIso U K ≪≫ (pull (D.opensRestrict U).proj).mapIso σ) n
    ((D.opensRestrict U).subsingleton_shiftedHom_diagonalObject hKU.isIso_diagonalAction hn)

/-- Relative perfectness of `K|_U` from an identification with a relative dualizing complex. -/
theorem IsRelativeDualizingComplex.isPerfectRelativeTo_of_iso (U : X.Opens) (K : Std X)
    {KU : Std U} {ξ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU}
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U) KU ξ)
    (σ : (pull U.ι).obj K ≅ KU) :
    (U.ι ≫ f).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback U.ι.toLRSHom.toShHom).obj K) := by
  obtain ⟨⟨P, hP, ⟨g⟩⟩, h₂⟩ := hKU.isPerfectRelativeTo
  exact ⟨⟨P, hP, ⟨g ≪≫ σ.symm⟩⟩,
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_iso
      ((Scheme.Hom.derivedScalarRestriction (U.ι ≫ f)).mapIso σ.symm) h₂⟩

/-- The map defined by a glued `ψ` is invertible on a chart on which `ψ` restricts to the chart map
of a relative dualizing complex. -/
theorem IsRelativeDualizingComplex.isIso_pull_diagonalAction_of_chartHom (U : X.Opens)
    (K : Std X) {KU : Std U}
    {ξ : ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
      (pull (D.opensRestrict U).proj).obj KU}
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U) KU ξ)
    (σ : (pull U.ι).obj K ≅ KU) (ψ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hψ : (pull (D.squareOpens U).ι).map ψ = D.chartHom U K ξ σ) :
    IsIso ((derivedPullback (D.squareOpens U).ι.toLRSHom.toShHom).map
      (D.diagonalAction K ψ)) := by
  have h₁ := IsRelativeDualizingComplex.isIso_diagonalAction_comp hKU.isIso_diagonalAction σ.symm
  have h₂ : (D.squareDiagonalIso U).inv ≫ (pull (D.squareOpens U).ι).map ψ ≫
      (D.squareProjIso U K).hom =
      ξ ≫ (D.opensRestrict U).derivedPullbackProjMap σ.symm.hom :=
    (congrArg (fun m => (D.squareDiagonalIso U).inv ≫ m ≫ (D.squareProjIso U K).hom) hψ).trans
      (D.chartHom_cancel U K ξ σ)
  exact D.isIso_pull_diagonalAction_of_transport K (D.opensRestrict U) ((pull U.ι).obj K)
    (D.squareOpens U).ι ψ (D.squareDiagonalIso U) (D.squareProjIso U K)
    (D.diagonalObjectPullIso_mul (D.opensRestrict U) (D.squareOpens U).ι U.ι
      (D.isPullback_opensRestrictDiag U))
    (Eq.mpr (congrArg (fun x => IsIso ((D.opensRestrict U).diagonalAction ((pull U.ι).obj K) x))
      h₂) h₁)

/-- Relative perfectness of an object identified on the charts with relative dualizing
complexes. -/
theorem isPerfectRelativeTo_of_charts (K : Std X) {KU : ∀ U ∈ chartOpens f, Std U}
    {ξU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
        (pull (D.opensRestrict U).proj).obj (KU U hU)}
    (hKU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U)
        (KU U hU) (ξU U hU))
    (σ : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), (pull U.ι).obj K ≅ KU U hU) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K := by
  refine isPerfectRelativeTo_of_openImmersion_cover f (fun U : chartOpens f => U.1.toScheme)
    (fun U => U.1.ι) (fun x => ?_) K (fun U =>
      (hKU U.1 U.2).isPerfectRelativeTo_of_iso D U.1 K (σ U.1 U.2))
  obtain ⟨U, hU, hxU⟩ := DiagonalOpen.exists_mem_chartOpens (f := f) x
  exact ⟨⟨U, hU⟩, by rw [Scheme.Opens.range_ι]; exact hxU⟩

/-- The diagonal condition for a morphism restricting on the charts to chart maps of relative
dualizing complexes. -/
theorem isIso_diagonalAction_of_charts (K : Std X) {KU : ∀ U ∈ chartOpens f, Std U}
    {ξU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
        (pull (D.opensRestrict U).proj).obj (KU U hU)}
    (hKU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U)
        (KU U hU) (ξU U hU))
    (σ : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), (pull U.ι).obj K ≅ KU U hU)
    (ψ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hψ : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      (pull (D.squareOpens U).ι).map ψ = D.chartHom U K (ξU U hU) (σ U hU)) :
    IsIso (D.diagonalAction K ψ) := by
  refine D.isIso_diagonalAction_of_cover K ψ (fun U : chartOpens f => (D.squareOpens U.1).ι)
    (fun x => ?_) (fun U => (hKU U.1 U.2).isIso_pull_diagonalAction_of_chartHom D U.1 K
      (σ U.1 U.2) ψ (hψ U.1 U.2))
  obtain ⟨U, hU, hxU⟩ := DiagonalOpen.exists_mem_chartOpens (f := f) x
  exact ⟨⟨U, hU⟩, by rw [Scheme.Opens.range_ι]; exact (D.diag_mem_squareOpens_iff x).2 hxU⟩

/-- Glueing the chart maps on `W`. -/
theorem exists_hom_of_charts (K : Std X) {KU : ∀ U ∈ chartOpens f, Std U}
    {ξU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
        (pull (D.opensRestrict U).proj).obj (KU U hU)}
    (hKU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U)
        (KU U hU) (ξU U hU))
    (σ : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), (pull U.ι).obj K ≅ KU U hU)
    (hσ : ∀ (V U : X.Opens) (h : V ≤ U) (hU : U ∈ chartOpens f) (hV : V ∈ chartOpens f),
      D.squareTransport h (ξU U hU) ≫ (pull (D.opensRestrict V).proj).map
        ((pull (X.homOfLE h)).map (σ U hU).inv ≫
          (Scheme.DerivedPullbackOpensGlueing.resComp h K).hom ≫ (σ V hV).hom) = ξU V hV) :
    ∃ ψ : D.diagonalObject ⟶ D.derivedPullbackProj K, ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      (pull (D.squareOpens U).ι).map ψ = D.chartHom U K (ξU U hU) (σ U hU) :=
  D.exists_hom_of_squareOpens D.isZero_pull_diagonalObject
    (fun U hU => D.chartHom U K (ξU U hU) (σ U hU))
    (fun U hU V hV h => D.chartHom_restrict h K (ξU U hU) (ξU V hV) (σ U hU) (σ V hV)
      (hσ V U h hU hV))
    (fun U hU _n hn => (hKU U hU).subsingleton_shiftedHom_squareOpens D U K (σ U hU) hn)

/-- **Assembling a relative dualizing complex from relative dualizing complexes on the charts**
(proof of Stacks 0E2X): glue the `K_U` by the BBD lemma, glue the maps `ξ_U` on `W` along the
charts `W ∩ (U ×_S U)`, and check both conditions locally. -/
theorem exists_isRelativeDualizingComplex_of_charts
    (KU : ∀ U ∈ chartOpens f, Std U)
    (ξU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f),
      ((D.opensRestrict U).diagonalObject : Std (D.opensRestrict U).W) ⟶
        (pull (D.opensRestrict U).proj).obj (KU U hU))
    (hKU : ∀ (U : X.Opens) (hU : U ∈ chartOpens f), IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.opensRestrict U)
        (KU U hU) (ξU U hU)) :
    ∃ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ := by
  obtain ⟨K, σ, hσ⟩ := exists_glueing_chart D KU ξU hKU
  obtain ⟨ψ, hψ⟩ := exists_hom_of_charts D K hKU σ hσ
  have h₁ := isPerfectRelativeTo_of_charts D K hKU σ
  have h₂ := isIso_diagonalAction_of_charts D K hKU σ ψ hψ
  refine ⟨K, ψ, ?_⟩
  constructor
  · exact h₁
  · exact h₂

/-- **Stacks 0E2X at the canonical families**: a flat, locally finitely presented morphism has a
relative dualizing complex relative to every diagonal open, `S`-perfectness being read at the
derived tensor product of Stacks 06YU. -/
theorem exists_isRelativeDualizingComplex_canonicalFamily :
    ∃ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ := by
  choose KU ξU hKU using fun U (hU : U ∈ chartOpens f) =>
    let ⟨hUa, V, hV, hUV⟩ := hU
    exists_isRelativeDualizingComplex_chart f hUa hV hUV (D.opensRestrict U)
  exact exists_isRelativeDualizingComplex_of_charts D KU ξU hKU

/-- `exists_isRelativeDualizingComplex_canonicalFamily`, unfolded: `K` is relatively perfect in the
sense of Stacks 0DI0 and `ξ` satisfies the diagonal condition. -/
theorem exists_isRelativelyPerfect_isIso_diagonalAction :
    ∃ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      f.IsRelativelyPerfect K ∧ IsIso (D.diagonalAction K ξ) := by
  obtain ⟨K, ξ, hK⟩ := exists_isRelativeDualizingComplex_canonicalFamily D
  exact ⟨K, ξ, hK.isPerfectRelativeTo, hK.isIso_diagonalAction⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 0E2X.** Let `f : X ⟶ S` be flat and locally of finite presentation. There exists a
relative dualizing complex `(K, ξ)` (Stacks 0E2T), relative to any open `W ⊆ X ×_S X` through
which the relative diagonal factors as a closed immersion: `K ∈ D(𝒪_X)` is `S`-perfect and
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` defines an isomorphism
`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

`S`-perfectness is read at a family `Dten` of derived tensor products on the open subspaces of
`(X, f⁻¹𝒪_S)` whose underived tensor products are those of sheaves of modules, so that it is
Stacks 0DI0 (`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_isRelativelyPerfect`).

The derived categories of the inverse-image ringed spaces `(X, f⁻¹𝒪_S)|_U` are those of
`CategoryTheory.HasDerivedCategory.standard`, the model at which the chart step (Stacks 0E2F read
through Stacks 0E2U, `exists_isRelativeDualizingComplex_chart`), the restriction of relative
dualizing complexes and Stacks 0E2W are stated. They cannot be left arbitrary: the Tor clause of
`S`-perfectness is read on `(derivedScalarRestriction f).obj K` in the chosen model of
`D(f⁻¹𝒪_S)`, and carrying it from one model to another needs the comparison of the two models of
the derived category, which the library does not provide. -/
@[stacks 0E2X]
theorem exists_isRelativeDualizingComplex [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f Dten) (D : DiagonalOpen f) :
    ∃ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex f Dten D K ξ := by
  obtain ⟨K, ξ, hK⟩ := exists_isRelativeDualizingComplex_canonicalFamily D
  exact ⟨K, ξ, (isRelativeDualizingComplex_iff_canonicalFamily f Dten hD D K ξ).2 hK⟩

end AlgebraicGeometry.Scheme.Hom

end
