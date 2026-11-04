module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekComposition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionAssociativity
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Exceptional inverse image is a pseudofunctor (Tag 0ATY): the diagram chase

In the situation of [Stacks, Tag 0F42] — a Noetherian base `S` and the category
`AlgebraicGeometry.FTS S` of schemes separated and of finite type over `S` — [Stacks, Tag 0ATY]
says that the constructions of [Stacks, Tag 0AA0] (the functor `f^!` of a compactification) and
[Stacks, Tag 0ATX] (the canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!`) define a pseudofunctor from
`FTS S` into the 2-category of categories, in the sense of Categories, Definition 4.29.5
([Stacks, Tag 003N]). This part contains the cocycle identity of derived pullback
(`Stacks.Duality.pbCompN_cocycle`), the coherences of the twisted inverse image as identities of
transformations, and the diagram chase of the source with every functor and transformation a
variable (`Stacks.Duality.tripleChase`, `Stacks.Duality.compositionChaseNat`,
`Stacks.Duality.cocycleTransport`), together with the unit `Stacks.Duality.unitOf` and the laws
`Stacks.Duality.catAssoc`, `Stacks.Duality.catLeft`, `Stacks.Duality.catRight` used to assemble
the pseudofunctor.

## The proof

The source chooses a compactification `Z̄` of `Z` over `T`, then `Ȳ` of `Y` over `Z̄`, then `X̄`
of `X` over `Ȳ` (More on Flatness, Theorem 0F41 and Lemma 0A9Z); here these are a
`Stacks.Duality.CompositionData` `E` for `g` and `h` and a compactification `t` of `X` over `Ȳ`,
from which `Stacks.Duality.CompositionData.tripleLeft`, `tripleRight` and `tripleInner` are the
choices for `(f, h ∘ g)`, `(g ∘ f, h)` and `(f, g)`. With `W ⊂ Ȳ` the inverse image of `Z` and
`V ⊂ X̄`, `U' ⊂ V` the inverse images of `W` and `Y`, the squares `A` (`U' ⟶ V` over `Y ⟶ W`),
`B` (`V ⟶ X̄` over `W ⟶ Ȳ`) and `C` (`W ⟶ Ȳ` over `Z ⟶ Z̄`) are cartesian. The chase,
`Stacks.Duality.tripleChase`, uses `γ_{A+B} = γ_A ∘ γ_B` ([Stacks, Tag 0ATR],
`Stacks.Duality.CompositionData.tripleRowNat`), `γ_{B+C} = γ_C ∘ γ_B` ([Stacks, Tag 0ATQ],
`Stacks.Duality.CompositionData.tripleStackNat`), the coherence of the comparisons for the twisted
inverse image (`Stacks.Duality.CompositionData.tripleCocycle`), and the commutation of `γ_A` and
`γ_C`, which is naturality.

The source silently identifies the inverse image `U` of `Y` in `X̄` (which the choice for
`(f, h ∘ g)` uses) with its inverse image `U'` in `V` (which the choice for `(f, g)` uses). Here
the two are compared by the isomorphism `Stacks.Duality.CompositionData.tripleComparison`, and the
comparison is an instance of the chase of [Stacks, Tag 0ATX]
(`Stacks.Duality.CompositionData.triplePsi`, from `Stacks.Duality.compositionChaseNat`); it
needs the cocycle identity of derived pullback, `Stacks.Duality.pbCompN_cocycle`. The canonical
comparisons of [Stacks, Tag 0AA0] then move the identity to arbitrary compactifications
(`Stacks.Duality.cocycleTransport`).

*The unit.* The unit `(𝟙_X)^! ≅ id` is not specified by the source. It is taken to be
`Stacks.Duality.unitOf` of the compositor of `𝟙_X`, an isomorphism whose component at
`(𝟙_X)^! K` is the inverse of that compositor; the two unit conditions then follow from the
cocycle condition (`Stacks.Duality.unitOf_left`, `Stacks.Duality.unitOf_right`). An isomorphism
`(𝟙_X)^! ≅ id` to start from is `Stacks.Duality.chosenUpperShriekPlusIdIso`, through the
compactification `X` of the identity.

## Implementation notes

Every identity between the derived functors is proved with the categories and functors as
variables and then instantiated, and every instantiation is an identity of natural
transformations or of isomorphisms, never of components: a comparison of two spellings of the
same scheme morphism inside `.app` makes the kernel unfold the derived functors (see the module
documentation of `StacksFrontier/AlgebraicGeometry/Duality/Compactification/ShriekComposition.lean`).
For the same reason several open-immersion instances are passed explicitly, with the spelling of
the objects they are needed at.

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.Duality

section PullbackCocycle

variable {A B C D : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]
  [IsNoetherian D]

/-- The composition formula for derived pullback between Noetherian schemes is the left adjoint
composition isomorphism of the one for derived direct image. -/
theorem pbCompN_eq (p : A ⟶ B) (q : B ⟶ C) :
    pbCompN p q = Adjunction.leftAdjointCompIso
      (quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
        (noethPush q))
      (quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
        (noethPush p))
      (quasiCoherentDerivedAdjunction (p ≫ q) (isQuasicoherent_homology_derivedPullback' (p ≫ q))
        (noethPush (p ≫ q)))
      (quasiCoherentDerivedPushforwardCompIso p q (noethPush p) (noethPush q)
        (noethPush (p ≫ q))) := rfl

/-- **The cocycle identity for the composition formula of derived pullback** between Noetherian
schemes: the two identifications of `Ls^* ⋙ Lq^* ⋙ Lp^*` with `L(p ≫ q ≫ s)^*` agree. It is the
conjugate of the cocycle identity for derived direct image. -/
theorem pbCompN_cocycle (p : A ⟶ B) (q : B ⟶ C) (s : C ⟶ D) :
    isoWhiskerLeft (pb s) (pbCompN p q) ≪≫ pbCompN (p ≫ q) s =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (pbCompN q s) (pb p) ≪≫
        pbCompN p (q ≫ s) := by
  have h := quasiCoherentDerivedPushforwardCompIso_hom_assoc_whiskering p q s (noethPush p)
      (noethPush q)
    (noethPush s) (noethPush (p ≫ q)) (noethPush (q ≫ s)) (noethPush (p ≫ q ≫ s))
  have e : isoWhiskerLeft (quasiCoherentDerivedPushforward p (noethPush p))
        (quasiCoherentDerivedPushforwardCompIso q s (noethPush q) (noethPush s)
          (noethPush (q ≫ s))) ≪≫
      quasiCoherentDerivedPushforwardCompIso p (q ≫ s) (noethPush p) (noethPush (q ≫ s))
        (noethPush (p ≫ q ≫ s)) =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (quasiCoherentDerivedPushforwardCompIso p q (noethPush p) (noethPush q)
          (noethPush (p ≫ q))) (quasiCoherentDerivedPushforward s (noethPush s)) ≪≫
        quasiCoherentDerivedPushforwardCompIso (p ≫ q) s (noethPush (p ≫ q)) (noethPush s)
          (noethPush (p ≫ q ≫ s)) := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    rw [h]
    simp
  rw [pbCompN_eq, pbCompN_eq, pbCompN_eq, pbCompN_eq]
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ e

/-- The components of a cocycle identity of composition isomorphisms, with variable data and
with transports `τᵢ` that are identities. -/
theorem cocycleShape_app {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] {Pb : C₀ ⥤ C₁} {Pa : C₁ ⥤ C₂} {Pi : C₂ ⥤ C₃} {Pia : C₁ ⥤ C₃} {Pab : C₀ ⥤ C₂}
    {Piab : C₀ ⥤ C₃} (μia : Pa ⋙ Pi ≅ Pia) (μab : Pb ⋙ Pa ≅ Pab) (μ₁ : Pb ⋙ Pia ≅ Piab)
    (μ₂ : Pab ⋙ Pi ≅ Piab)
    (hc : isoWhiskerLeft Pb μia ≪≫ μ₁ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight μab Pi ≪≫ μ₂)
    (τ₁ τ₂ : Piab ≅ Piab) (τ₃ : Pia ≅ Pia) (h₁ : τ₁ = Iso.refl _) (h₂ : τ₂ = Iso.refl _)
    (h₃ : τ₃ = Iso.refl _) (P : C₀) :
    (τ₁ ≪≫ μ₂.symm).hom.app P ≫ Pi.map (μab.inv.app P) =
      (τ₂ ≪≫ μ₁.symm).hom.app P ≫ (τ₃ ≪≫ μia.symm).hom.app (Pb.obj P) := by
  subst h₁ h₂ h₃
  have hc' := congrArg (fun e => e.inv.app P) hc
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hc'
  simp only [Iso.refl_trans, Iso.symm_hom]
  exact hc'.symm

/-- The cocycle identity of `Stacks.Duality.pbCompN`, read through transports along equalities
of morphisms: for `x = j ≫ b` and `j = i ≫ a`, splitting `Lx^*` as `Lb^*` then `Lj^*` and then
`Lj^*` as `La^*` then `Li^*` is splitting it as `L(a ≫ b)^*` then `Li^*` and then `L(a ≫ b)^*`
as `Lb^*` then `La^*`. -/
theorem pbCompN_cocycle_app {A' : Scheme.{u}} [IsNoetherian A'] (i : A' ⟶ A) (a : A ⟶ B)
    (b : B ⟶ C) (j : A' ⟶ B) (x : A' ⟶ C) (hj : j = i ≫ a) (hx : x = j ≫ b)
    (hx' : x = i ≫ a ≫ b) (P : quasiCoherentDerivedCategory C) :
    (pbCongrN hx' ≪≫ (pbCompN i (a ≫ b)).symm).hom.app P ≫ (pb i).map ((pbCompN a b).inv.app P) =
      (pbCongrN hx ≪≫ (pbCompN j b).symm).hom.app P ≫
        (pbCongrN hj ≪≫ (pbCompN i a).symm).hom.app ((pb b).obj P) := by
  cases hj
  cases hx
  exact cocycleShape_app _ _ _ _ (pbCompN_cocycle i a b) _ _ _ (pbCongrN_self _) (pbCongrN_self _)
    (pbCongrN_self _) P

/-- The composition formula for derived pullback along equal first factors. -/
theorem pbCompN_congr_app {A' : Scheme.{u}} [IsNoetherian A'] {j j' : A' ⟶ B} (e : j = j')
    (b : B ⟶ C) (e' : j ≫ b = j' ≫ b) (P : quasiCoherentDerivedCategory C) :
    (pbCompN j b).inv.app P ≫ (pbCongrN e).hom.app ((pb b).obj P) =
      (pbCongrN e').hom.app P ≫ (pbCompN j' b).inv.app P := by
  subst e
  simp only [pbCongrN_self, Iso.refl_hom, NatTrans.id_app]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `Stacks.Duality.pbCompN_cocycle_app` as an identity of transformations. -/
theorem pbCompN_cocycle_nat {A' : Scheme.{u}} [IsNoetherian A'] (i : A' ⟶ A) (a : A ⟶ B)
    (b : B ⟶ C) (j : A' ⟶ B) (x : A' ⟶ C) (hj : j = i ≫ a) (hx : x = j ≫ b)
    (hx' : x = i ≫ a ≫ b) :
    (pbCongrN hx' ≪≫ (pbCompN i (a ≫ b)).symm).hom ≫ whiskerRight (pbCompN a b).inv (pb i) =
      (pbCongrN hx ≪≫ (pbCompN j b).symm).hom ≫
        whiskerLeft (pb b) (pbCongrN hj ≪≫ (pbCompN i a).symm).hom :=
  NatTrans.ext (funext fun P => pbCompN_cocycle_app i a b j x hj hx hx' P)

end PullbackCocycle

section TwistedCoherenceNat

variable {X₁ X₂ Y₁ Y₂ Zs : Scheme.{u}} [IsNoetherian X₁] [IsNoetherian X₂] [IsNoetherian Y₁]
  [IsNoetherian Y₂] [IsNoetherian Zs]

/-- `Stacks.Duality.compN_square` as an identity of transformations. -/
theorem compN_square_nat (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) (e : X₁ ⟶ X₂) (d : Y₁ ⟶ Y₂)
    (b₁ : Y₁ ⟶ Zs) (b₂ : Y₂ ⟶ Zs) (hb : d ≫ b₂ = b₁) (hpe : p₁ ≫ d = e ≫ p₂)
    (hk : p₁ ≫ b₁ = e ≫ p₂ ≫ b₂) :
    (congrN hk ≪≫ compN e (p₂ ≫ b₂)).hom ≫ whiskerRight (compN p₂ b₂).hom (tw e) =
      (compN p₁ b₁).hom ≫ whiskerRight (congrN hb.symm ≪≫ compN d b₂).hom (tw p₁) ≫
        whiskerLeft (tw b₂) ((compN p₁ d).inv ≫ (congrN hpe).hom ≫ (compN e p₂).hom) :=
  NatTrans.ext (funext fun K => compN_square p₁ p₂ e d b₁ b₂ hb hpe hk K)

/-- `Stacks.Duality.compN_unit` as an identity of transformations. -/
theorem compN_unit_nat (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₁) (e' : X₁ ⟶ X₂) (hq : e' ≫ q₂ = q₁)
    (hq' : q₁ ≫ 𝟙 Y₁ = e' ≫ q₂) :
    (congrN hq.symm ≪≫ compN e' q₂).hom =
      whiskerRight (idN Y₁).inv (tw q₁) ≫ (compN q₁ (𝟙 Y₁)).inv ≫ (congrN hq').hom ≫
        (compN e' q₂).hom :=
  NatTrans.ext (funext fun M => compN_unit q₁ q₂ e' hq hq' M)

end TwistedCoherenceNat

/-! ### The diagram chase of the source, with variable data -/

section Chase

variable {𝒯 𝒵b 𝒴b 𝒳b 𝒵 𝒲 𝒱 𝒴 𝒰 𝒳 : Type*} [Category 𝒯] [Category 𝒵b] [Category 𝒴b]
  [Category 𝒳b] [Category 𝒵] [Category 𝒲] [Category 𝒱] [Category 𝒴] [Category 𝒰] [Category 𝒳]

/-- **The diagram chase of the proof of [Stacks, Tag 0ATY]**, with every functor and every
transformation a variable. In the source's notation the hypotheses are:

* `H1` — the comparisons of [Stacks, Tag 0ATX] for the twisted inverse image are coherent;
* `H2` — `γ_{B+C} = γ_C ∘ γ_B`, [Stacks, Tag 0ATQ] for the stack of `B` over `C`;
* `H3` — `γ_{A+B} = γ_A ∘ γ_B`, [Stacks, Tag 0ATR] for the row of `A` and `B`.

The remaining step of the source, that `γ_A` and `γ_C` commute "because the two squares `A` and
`C` only intersect in one point", is the naturality of the transformations involved. The
conclusion, read at an object `T`, is the commutativity of the square of the source for the
comparisons of the choice of `f` and `h ∘ g` followed by the one of `g` and `h`, and of the choice
of `g ∘ f` and `h` followed by the one of `f` and `g`. -/
theorem tripleChase {c : 𝒯 ⥤ 𝒵b} {b : 𝒵b ⥤ 𝒴b} {a : 𝒴b ⥤ 𝒳b} {BC : 𝒯 ⥤ 𝒴b} {AB : 𝒵b ⥤ 𝒳b}
    {K : 𝒯 ⥤ 𝒳b} {iX : 𝒳b ⥤ 𝒳} {iY : 𝒴b ⥤ 𝒴} {iZ : 𝒵b ⥤ 𝒵} {w1 : 𝒴b ⥤ 𝒲} {iW : 𝒲 ⥤ 𝒴}
    {v1 : 𝒳b ⥤ 𝒱} {iV : 𝒱 ⥤ 𝒳} {u' : 𝒱 ⥤ 𝒰} {iU : 𝒰 ⥤ 𝒳} {uv : 𝒳b ⥤ 𝒰} {qW : 𝒵 ⥤ 𝒲}
    {qV : 𝒵 ⥤ 𝒱} {r : 𝒲 ⥤ 𝒱} {RQ : 𝒵 ⥤ 𝒱} {qU : 𝒴 ⥤ 𝒰}
    (cK₁ : K ≅ BC ⋙ a) (cBC : BC ≅ c ⋙ b) (cK₂ : K ≅ c ⋙ AB) (cAB : AB ≅ b ⋙ a)
    (cRQ : RQ ≅ qW ⋙ r) (e : qV ≅ RQ)
    (R1 : iX ≅ uv ⋙ iU) (Rgh : iY ≅ w1 ⋙ iW) (R2 : iX ≅ v1 ⋙ iV) (R3 : iV ≅ u' ⋙ iU)
    (β1 : a ⋙ uv ⟶ iY ⋙ qU) (βC : b ⋙ w1 ⟶ iZ ⋙ qW) (βV : AB ⋙ v1 ⟶ iZ ⋙ qV)
    (βA : r ⋙ u' ⟶ iW ⋙ qU) (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (H1 : ∀ T, cK₁.hom.app T ≫ a.map (cBC.hom.app T) = cK₂.hom.app T ≫ cAB.hom.app (c.obj T))
    (H2 : ∀ N, βV.app N ≫ e.hom.app (iZ.obj N) ≫ cRQ.hom.app (iZ.obj N) =
      v1.map (cAB.hom.app N) ≫ βB.app (b.obj N) ≫ r.map (βC.app N))
    (H3 : ∀ N, R1.hom.app (a.obj N) ≫ iU.map (β1.app N) ≫ iU.map (qU.map (Rgh.hom.app N)) =
      R2.hom.app (a.obj N) ≫ iV.map (βB.app N) ≫ R3.hom.app (r.obj (w1.obj N)) ≫
        iU.map (βA.app (w1.obj N)))
    (T : 𝒯) :
    (iX.map (cK₁.hom.app T) ≫ R1.hom.app (a.obj (BC.obj T)) ≫ iU.map (β1.app (BC.obj T))) ≫
        iU.map (qU.map (iY.map (cBC.hom.app T) ≫ Rgh.hom.app (b.obj (c.obj T)) ≫
          iW.map (βC.app (c.obj T)))) =
      (iX.map (cK₂.hom.app T) ≫ R2.hom.app (AB.obj (c.obj T)) ≫ iV.map (βV.app (c.obj T))) ≫
        iV.map (e.hom.app (iZ.obj (c.obj T))) ≫
          (iV.map (cRQ.hom.app (iZ.obj (c.obj T))) ≫
            R3.hom.app (r.obj (qW.obj (iZ.obj (c.obj T)))) ≫
              iU.map (βA.app (qW.obj (iZ.obj (c.obj T))))) := by
  have n1 := congrArg iU.map (β1.naturality (cBC.hom.app T))
  have nR1 := R1.hom.naturality (a.map (cBC.hom.app T))
  have nR2 := R2.hom.naturality (cAB.hom.app (c.obj T))
  have nR3 := R3.hom.naturality (r.map (βC.app (c.obj T)))
  have nA := congrArg iU.map (βA.naturality (βC.app (c.obj T)))
  have h2 := congrArg iV.map (H2 (c.obj T))
  have h3 := H3 (b.obj (c.obj T))
  have h1 := H1 T
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at n1 nR1 nR2 nR3 nA h2 h3 h1
  calc _ = iX.map (cK₁.hom.app T ≫ a.map (cBC.hom.app T)) ≫
        (R1.hom.app (a.obj (b.obj (c.obj T))) ≫ iU.map (β1.app (b.obj (c.obj T))) ≫
          iU.map (qU.map (Rgh.hom.app (b.obj (c.obj T))))) ≫
          iU.map (qU.map (iW.map (βC.app (c.obj T)))) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← reassoc_of% n1, ← reassoc_of% nR1]
    _ = iX.map (cK₂.hom.app T ≫ cAB.hom.app (c.obj T)) ≫
        (R2.hom.app (a.obj (b.obj (c.obj T))) ≫ iV.map (βB.app (b.obj (c.obj T))) ≫
          R3.hom.app (r.obj (w1.obj (b.obj (c.obj T)))) ≫
            iU.map (βA.app (w1.obj (b.obj (c.obj T))))) ≫
          iU.map (qU.map (iW.map (βC.app (c.obj T)))) := by rw [h1, h3]
    _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% h2, reassoc_of% nR2, reassoc_of% nR3, nA]

/-- The shape of the hypothesis `H2` of `Stacks.Duality.tripleChase`: the base change map of a
square read along a transport of its left edge, and [Stacks, Tag 0ATQ] for that square split as a
stack. -/
theorem stackCongrShape {b : 𝒵b ⥤ 𝒴b} {a : 𝒴b ⥤ 𝒳b} {AB : 𝒵b ⥤ 𝒳b} {iZ : 𝒵b ⥤ 𝒵}
    {w1 : 𝒴b ⥤ 𝒲} {v1 : 𝒳b ⥤ 𝒱} {qW : 𝒵 ⥤ 𝒲} {qV : 𝒵 ⥤ 𝒱} {r : 𝒲 ⥤ 𝒱} {RQ : 𝒵 ⥤ 𝒱}
    (cAB : AB ≅ b ⋙ a) (cRQ : RQ ≅ qW ⋙ r) (e : qV ≅ RQ) (τ : AB ≅ AB) (hτ : τ = Iso.refl _)
    (βC : b ⋙ w1 ⟶ iZ ⋙ qW) (βV : AB ⋙ v1 ⟶ iZ ⋙ qV) (βP : AB ⋙ v1 ⟶ iZ ⋙ RQ)
    (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (hv : ∀ N, βV.app N = v1.map (τ.hom.app N) ≫ βP.app N ≫ e.inv.app (iZ.obj N))
    (hs : ∀ N, βP.app N = v1.map (cAB.hom.app N) ≫ βB.app (b.obj N) ≫ r.map (βC.app N) ≫
      cRQ.inv.app (iZ.obj N)) (N : 𝒵b) :
    βV.app N ≫ e.hom.app (iZ.obj N) ≫ cRQ.hom.app (iZ.obj N) =
      v1.map (cAB.hom.app N) ≫ βB.app (b.obj N) ≫ r.map (βC.app N) := by
  subst hτ
  rw [hv, hs]
  simp

/-- The shape of the hypothesis `H3` of `Stacks.Duality.tripleChase`: [Stacks, Tag 0ATR] for the
row of the squares `A` and `B`, together with the cocycle identity of derived pullback for the
three open immersions `X ⟶ U' ⟶ V ⟶ X̄`. -/
theorem rowCocycleShape {a : 𝒴b ⥤ 𝒳b} {iX : 𝒳b ⥤ 𝒳} {iY : 𝒴b ⥤ 𝒴} {w1 : 𝒴b ⥤ 𝒲}
    {iW : 𝒲 ⥤ 𝒴} {v1 : 𝒳b ⥤ 𝒱} {iV : 𝒱 ⥤ 𝒳} {u' : 𝒱 ⥤ 𝒰} {iU : 𝒰 ⥤ 𝒳} {uv : 𝒳b ⥤ 𝒰}
    {r : 𝒲 ⥤ 𝒱} {qU : 𝒴 ⥤ 𝒰}
    (R1 : iX ≅ uv ⋙ iU) (Rgh : iY ≅ w1 ⋙ iW) (R2 : iX ≅ v1 ⋙ iV) (R3 : iV ≅ u' ⋙ iU)
    (ω₁ : v1 ⋙ u' ≅ uv) (β1 : a ⋙ uv ⟶ iY ⋙ qU) (βA : r ⋙ u' ⟶ iW ⋙ qU)
    (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (hrow : ∀ M, β1.app M = (Iso.refl uv ≪≫ ω₁.symm).hom.app (a.obj M) ≫ u'.map (βB.app M) ≫
      βA.app (w1.obj M) ≫ qU.map (Rgh.inv.app M))
    (hcoc : ∀ P, R1.hom.app P ≫ iU.map (ω₁.inv.app P) = R2.hom.app P ≫ R3.hom.app (v1.obj P))
    (N : 𝒴b) :
    R1.hom.app (a.obj N) ≫ iU.map (β1.app N) ≫ iU.map (qU.map (Rgh.hom.app N)) =
      R2.hom.app (a.obj N) ≫ iV.map (βB.app N) ≫ R3.hom.app (r.obj (w1.obj N)) ≫
        iU.map (βA.app (w1.obj N)) := by
  have nR3 := R3.hom.naturality (βB.app N)
  simp only [Functor.comp_obj, Functor.comp_map] at nR3
  rw [reassoc_of% nR3, ← reassoc_of% (hcoc (a.obj N)), hrow]
  simp only [Iso.refl_trans, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← iU.map_comp, ← qU.map_comp, Iso.inv_hom_id_app]
  simp

variable {𝒜 ℬ 𝒞 𝒟 ℰ 𝒢 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  [Category ℰ] [Category 𝒢]

open scoped CategoryTheory.TwoSquare in
/-- Reading the row identity of [Stacks, Tag 0ATR], transported along equalities of the
horizontal edges, at an object, for a row whose left edge is arbitrary. -/
theorem rowChaseGen {Ee : 𝒜 ⥤ ℬ} {C₁ L₁ : ℬ ⥤ 𝒞} {C₂ L₂ : 𝒜 ⥤ 𝒢} {F₁ : ℬ ⥤ 𝒟} {F₂ : 𝒜 ⥤ ℰ}
    {V₁ : 𝒟 ⥤ 𝒞} {V₂ : ℰ ⥤ 𝒢} {Ee' : ℰ ⥤ 𝒟} {IX : 𝒢 ⥤ 𝒞}
    (τ₁ : C₁ ≅ L₁) (τ₂ : C₂ ≅ L₂) (ω₁ : F₁ ⋙ V₁ ≅ L₁) (ω₂ : F₂ ⋙ V₂ ≅ L₂)
    (pc₁ : C₁ ≅ F₁ ⋙ V₁) (pc₂ : C₂ ≅ F₂ ⋙ V₂) (hpc₁ : pc₁ = τ₁ ≪≫ ω₁.symm)
    (hpc₂ : pc₂ = τ₂ ≪≫ ω₂.symm)
    (βE : Ee ⋙ C₁ ⟶ C₂ ⋙ IX) (βrow : Ee ⋙ L₁ ⟶ L₂ ⋙ IX) (βF : Ee ⋙ F₁ ⟶ F₂ ⋙ Ee')
    (βA : Ee' ⋙ V₁ ⟶ V₂ ⋙ IX)
    (hE : βE = Functor.whiskerLeft Ee τ₁.hom ≫ βrow ≫ Functor.whiskerRight τ₂.inv IX)
    (hrow : βrow = (((TwoSquare.mk _ _ _ _ βF ≫ᵥ TwoSquare.mk _ _ _ _ βA).whiskerLeft
      ω₂.hom).whiskerRight ω₁.inv).natTrans) (M : 𝒜) :
    βE.app M = pc₁.hom.app (Ee.obj M) ≫ V₁.map (βF.app M) ≫ βA.app (F₂.obj M) ≫
      IX.map (pc₂.inv.app M) := by
  subst hpc₁ hpc₂ hE hrow
  simp [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

section NatShapes

open scoped CategoryTheory.TwoSquare

variable {𝒯 𝒵b 𝒴b 𝒳b 𝒵 𝒲 𝒱 𝒴 𝒰 𝒳 : Type*} [Category 𝒯] [Category 𝒵b] [Category 𝒴b]
  [Category 𝒳b] [Category 𝒵] [Category 𝒲] [Category 𝒱] [Category 𝒴] [Category 𝒰] [Category 𝒳]

/-- `Stacks.Duality.tripleChase` as an identity of transformations, with hypotheses that are
identities of transformations. -/
theorem tripleChaseNat {c : 𝒯 ⥤ 𝒵b} {b : 𝒵b ⥤ 𝒴b} {a : 𝒴b ⥤ 𝒳b} {BC : 𝒯 ⥤ 𝒴b}
    {AB : 𝒵b ⥤ 𝒳b} {K : 𝒯 ⥤ 𝒳b} {iX : 𝒳b ⥤ 𝒳} {iY : 𝒴b ⥤ 𝒴} {iZ : 𝒵b ⥤ 𝒵} {w1 : 𝒴b ⥤ 𝒲}
    {iW : 𝒲 ⥤ 𝒴} {v1 : 𝒳b ⥤ 𝒱} {iV : 𝒱 ⥤ 𝒳} {u' : 𝒱 ⥤ 𝒰} {iU : 𝒰 ⥤ 𝒳} {uv : 𝒳b ⥤ 𝒰}
    {qW : 𝒵 ⥤ 𝒲} {qV : 𝒵 ⥤ 𝒱} {r : 𝒲 ⥤ 𝒱} {RQ : 𝒵 ⥤ 𝒱} {qU : 𝒴 ⥤ 𝒰}
    (cK₁ : K ≅ BC ⋙ a) (cBC : BC ≅ c ⋙ b) (cK₂ : K ≅ c ⋙ AB) (cAB : AB ≅ b ⋙ a)
    (cRQ : RQ ≅ qW ⋙ r) (e : qV ≅ RQ)
    (R1 : iX ≅ uv ⋙ iU) (Rgh : iY ≅ w1 ⋙ iW) (R2 : iX ≅ v1 ⋙ iV) (R3 : iV ≅ u' ⋙ iU)
    (β1 : a ⋙ uv ⟶ iY ⋙ qU) (βC : b ⋙ w1 ⟶ iZ ⋙ qW) (βV : AB ⋙ v1 ⟶ iZ ⋙ qV)
    (βA : r ⋙ u' ⟶ iW ⋙ qU) (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (H1 : cK₁.hom ≫ whiskerRight cBC.hom a = cK₂.hom ≫ whiskerLeft c cAB.hom)
    (H2 : βV ≫ whiskerLeft iZ (e.hom ≫ cRQ.hom) =
      whiskerRight cAB.hom v1 ≫ whiskerLeft b βB ≫ whiskerRight βC r)
    (H3 : whiskerLeft a R1.hom ≫ whiskerRight β1 iU ≫ whiskerRight (whiskerRight Rgh.hom qU) iU =
      whiskerLeft a R2.hom ≫ whiskerRight βB iV ≫ whiskerLeft (w1 ⋙ r) R3.hom ≫
        whiskerLeft w1 (whiskerRight βA iU)) :
    chainMap cK₁.hom R1.hom β1 ≫ whiskerRight (chainMap cBC.hom Rgh.hom βC) (qU ⋙ iU) =
      chainMap cK₂.hom R2.hom βV ≫
        whiskerLeft (c ⋙ iZ) (whiskerRight e.hom iV ≫ chainMap cRQ.hom R3.hom βA) := by
  refine NatTrans.ext (funext fun T => ?_)
  have h := tripleChase cK₁ cBC cK₂ cAB cRQ e R1 Rgh R2 R3 β1 βC βV βA βB
    (fun T => by simpa using NatTrans.congr_app H1 T)
    (fun N => by simpa using NatTrans.congr_app H2 N)
    (fun N => by simpa using NatTrans.congr_app H3 N) T
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, chainMap_app,
    Functor.comp_map, Functor.comp_obj] at h ⊢
  simpa using h

/-- The shape of the hypothesis `H2` of `Stacks.Duality.tripleChaseNat`: the base change map of a
square read along a transport of its left edge, and [Stacks, Tag 0ATQ] for that square split as a
stack. -/
theorem stackNat {b : 𝒵b ⥤ 𝒴b} {a : 𝒴b ⥤ 𝒳b} {AB : 𝒵b ⥤ 𝒳b} {iZ : 𝒵b ⥤ 𝒵}
    {w1 : 𝒴b ⥤ 𝒲} {v1 : 𝒳b ⥤ 𝒱} {qW : 𝒵 ⥤ 𝒲} {qV : 𝒵 ⥤ 𝒱} {r : 𝒲 ⥤ 𝒱} {RQ : 𝒵 ⥤ 𝒱}
    (cAB : AB ≅ b ⋙ a) (cRQ : RQ ≅ qW ⋙ r) (e : qV ≅ RQ) (τ : AB ≅ AB) (hτ : τ = Iso.refl _)
    (βC : b ⋙ w1 ⟶ iZ ⋙ qW) (βV : AB ⋙ v1 ⟶ iZ ⋙ qV) (βP : AB ⋙ v1 ⟶ iZ ⋙ RQ)
    (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (hv : βV = whiskerRight τ.hom v1 ≫ βP ≫ whiskerLeft iZ e.inv)
    (hs : βP = ((TwoSquare.mk _ _ _ _ βC ≫ₕ TwoSquare.mk _ _ _ _ βB).whiskerTop
      cAB.hom).whiskerBottom cRQ.inv) :
    βV ≫ whiskerLeft iZ (e.hom ≫ cRQ.hom) =
      whiskerRight cAB.hom v1 ≫ whiskerLeft b βB ≫ whiskerRight βC r := by
  subst hτ hv hs
  ext N
  simp [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

variable {𝒜 ℬ 𝒞 𝒟 ℰ 𝒢 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  [Category ℰ] [Category 𝒢]

/-- The shape of the hypothesis `H3` of `Stacks.Duality.tripleChaseNat`: [Stacks, Tag 0ATR] for
the row of the squares `A` and `B`, transported along an equality of the bottom edge, together
with the cocycle identity of derived pullback for the open immersions `X ⟶ U' ⟶ V ⟶ X̄`. -/
theorem rowNat {a : 𝒴b ⥤ 𝒳b} {iX : 𝒳b ⥤ 𝒳} {iY L₂ : 𝒴b ⥤ 𝒴} {w1 : 𝒴b ⥤ 𝒲}
    {iW : 𝒲 ⥤ 𝒴} {v1 : 𝒳b ⥤ 𝒱} {iV : 𝒱 ⥤ 𝒳} {u' : 𝒱 ⥤ 𝒰} {iU : 𝒰 ⥤ 𝒳} {uv : 𝒳b ⥤ 𝒰}
    {r : 𝒲 ⥤ 𝒱} {qU : 𝒴 ⥤ 𝒰}
    (R1 : iX ≅ uv ⋙ iU) (R2 : iX ≅ v1 ⋙ iV) (R3 : iV ≅ u' ⋙ iU)
    (τ₁ : uv ≅ uv) (hτ₁ : τ₁ = Iso.refl _) (τ₂ : iY ≅ L₂) (ω₁ : v1 ⋙ u' ≅ uv)
    (ω₂ : w1 ⋙ iW ≅ L₂) (β1 : a ⋙ uv ⟶ iY ⋙ qU) (βrow : a ⋙ uv ⟶ L₂ ⋙ qU)
    (βA : r ⋙ u' ⟶ iW ⋙ qU) (βB : a ⋙ v1 ⟶ w1 ⋙ r)
    (hE : β1 = whiskerLeft a τ₁.hom ≫ βrow ≫ whiskerRight τ₂.inv qU)
    (hrow : βrow = (((TwoSquare.mk _ _ _ _ βB ≫ᵥ TwoSquare.mk _ _ _ _ βA).whiskerLeft
      ω₂.hom).whiskerRight ω₁.inv).natTrans)
    (hcoc : R1.hom ≫ whiskerRight ω₁.inv iU = R2.hom ≫ whiskerLeft v1 R3.hom) :
    whiskerLeft a R1.hom ≫ whiskerRight β1 iU ≫
        whiskerRight (whiskerRight (τ₂ ≪≫ ω₂.symm).hom qU) iU =
      whiskerLeft a R2.hom ≫ whiskerRight βB iV ≫ whiskerLeft (w1 ⋙ r) R3.hom ≫
        whiskerLeft w1 (whiskerRight βA iU) := by
  subst hτ₁ hE hrow
  ext N
  have hc := NatTrans.congr_app hcoc (a.obj N)
  have nR3 := R3.hom.naturality (βB.app N)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.comp_map] at hc nR3
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, Iso.refl_hom, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc, Functor.whiskerLeft_id', Category.id_comp]
  rw [reassoc_of% nR3, ← reassoc_of% hc]
  simp only [← Functor.map_comp,
    Iso.inv_hom_id_app_assoc]
  simp

/-- **`Stacks.Duality.compositionChase` with hypotheses and conclusion that are identities of
transformations**: the comparison `α_E` followed by the comparison of [Stacks, Tag 0ATX] built from
the second choice is the comparison built from the first choice followed by the comparisons `α_A`
and `α_D`. The hypotheses are those of the source's chase in the form [Stacks, Tag 0ATR],
[Stacks, Tag 0ATQ] and the coherence of the twisted inverse image provide them. -/
theorem compositionChaseNat
    {Zc Y₁c Y₂c X₁c X₂c U₁c U₂c Yc Xc : Type*}
    [Category Zc] [Category Y₁c] [Category Y₂c] [Category X₁c]
    [Category X₂c] [Category U₁c] [Category U₂c] [Category Yc] [Category Xc]
    {B₁ : Zc ⥤ Y₁c} {B₂ : Zc ⥤ Y₂c} {Dd : Y₂c ⥤ Y₁c}
    {P₁ : Y₁c ⥤ X₁c} {P₂ : Y₂c ⥤ X₂c} {Ee : X₂c ⥤ X₁c}
    {K₁ : Zc ⥤ X₁c} {K₂ : Zc ⥤ X₂c}
    {Q₁ : Yc ⥤ U₁c} {Q₂ : Yc ⥤ U₂c} {Ee' : U₂c ⥤ U₁c}
    {IY : Yc ⥤ Yc} {IX : Xc ⥤ Xc}
    {C₁ L₁ : X₁c ⥤ Xc} {C₂ L₂ : X₂c ⥤ Xc} {F₁ : X₁c ⥤ U₁c} {F₂ : X₂c ⥤ U₂c}
    {V₁ : U₁c ⥤ Xc} {V₂ : U₂c ⥤ Xc} {I₁ : Y₁c ⥤ Yc} {I₂ : Y₂c ⥤ Yc}
    {PD EP : Y₂c ⥤ X₁c} {QI EQ : Yc ⥤ U₁c}
    (cK₁ : K₁ ≅ B₁ ⋙ P₁) (cK₂ : K₂ ≅ B₂ ⋙ P₂)
    (τ₁ : C₁ ≅ L₁) (τ₂ : C₂ ≅ L₂) (ω₁ : F₁ ⋙ V₁ ≅ L₁) (ω₂ : F₂ ⋙ V₂ ≅ L₂)
    (pc₁ : C₁ ≅ F₁ ⋙ V₁) (pc₂ : C₂ ≅ F₂ ⋙ V₂) (hpc₁ : pc₁ = τ₁ ≪≫ ω₁.symm)
    (hpc₂ : pc₂ = τ₂ ≪≫ ω₂.symm)
    (βB₁ : P₁ ⋙ F₁ ⟶ I₁ ⋙ Q₁) (βB₂ : P₂ ⋙ F₂ ⟶ I₂ ⋙ Q₂)
    (eK : K₁ ≅ K₂ ⋙ Ee) (βE : Ee ⋙ C₁ ⟶ C₂ ⋙ IX) (uX : IX ≅ 𝟭 Xc)
    (eB : B₁ ≅ B₂ ⋙ Dd) (βD : Dd ⋙ I₁ ⟶ I₂ ⋙ IY) (uY : IY ≅ 𝟭 Yc)
    (eQ : Q₁ ≅ Q₂ ⋙ Ee') (βA : Ee' ⋙ V₁ ⟶ V₂ ⋙ IX)
    (βF : Ee ⋙ F₁ ⟶ F₂ ⋙ Ee') (βrow : Ee ⋙ L₁ ⟶ L₂ ⋙ IX)
    (cEP : EP ≅ P₂ ⋙ Ee) (cEQ : EQ ≅ Q₂ ⋙ Ee') (cPD : PD ≅ Dd ⋙ P₁) (cQI : QI ≅ IY ⋙ Q₁)
    (γP : PD ≅ EP) (γQ : QI ≅ EQ)
    (βFB : EP ⋙ F₁ ⟶ I₂ ⋙ EQ) (βCD : PD ⋙ F₁ ⟶ I₂ ⋙ QI)
    (hE : βE = Functor.whiskerLeft Ee τ₁.hom ≫ βrow ≫ Functor.whiskerRight τ₂.inv IX)
    (hrow : βrow = (((TwoSquare.mk _ _ _ _ βF ≫ᵥ TwoSquare.mk _ _ _ _ βA).whiskerLeft
      ω₂.hom).whiskerRight ω₁.inv).natTrans)
    (h₂ : βFB = ((TwoSquare.mk _ _ _ _ βB₂ ≫ₕ TwoSquare.mk _ _ _ _ βF).whiskerTop
      cEP.hom).whiskerBottom cEQ.inv)
    (h₃ : βCD = ((TwoSquare.mk _ _ _ _ βD ≫ₕ TwoSquare.mk _ _ _ _ βB₁).whiskerTop
      cPD.hom).whiskerBottom cQI.inv)
    (h₄ : βCD = Functor.whiskerRight γP.hom F₁ ≫ βFB ≫ Functor.whiskerLeft I₂ γQ.inv)
    (h₅ : eK.hom ≫ whiskerRight cK₂.hom Ee =
      cK₁.hom ≫ whiskerRight eB.hom P₁ ≫ whiskerLeft B₂ (cPD.inv ≫ γP.hom ≫ cEP.hom))
    (h₆ : eQ.hom = whiskerRight uY.inv Q₁ ≫ cQI.inv ≫ γQ.hom ≫ cEQ.hom) :
    alphaNat eK βE uX ≫ chainMap cK₂.hom pc₂.hom βB₂ =
      chainMap cK₁.hom pc₁.hom βB₁ ≫ Functor.whiskerLeft (B₁ ⋙ I₁) (alphaNat eQ βA uX) ≫
        Functor.whiskerRight (alphaNat eB βD uY) (Q₂ ⋙ V₂) := by
  refine naturalityShape eK βE uX eB βD uY eQ βA _ _ (fun K => ?_)
  rw [chainMap_app, chainMap_app]
  refine compositionChase cK₁ cK₂ pc₁ pc₂ βB₁ βB₂ eK βE uX eB βD uY eQ βA βF cEP cEQ cPD cQI
    γP γQ βFB βCD (rowChase τ₁ τ₂ ω₁ ω₂ pc₁ pc₂ hpc₁ hpc₂ βE βrow βF βA hE hrow)
    (stackChase βB₂ βF cEP cEQ βFB h₂) (stackChase βD βB₁ cPD cQI βCD h₃)
    (vertChase γP γQ βCD βFB h₄) (fun K => ?_) (fun M => ?_) K
  · simpa using NatTrans.congr_app h₅ K
  · simpa using NatTrans.congr_app h₆ M

/-- A whiskered transport along an equality of functors is a transport. -/
theorem whiskerLeft_whiskerRight_eqToHom {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] [Category 𝒟] (ι : 𝒜 ⥤ ℬ) {T₁ T₂ : ℬ ⥤ 𝒞} (P : 𝒞 ⥤ 𝒟) (p : T₁ = T₂) :
    whiskerLeft ι (whiskerRight (eqToHom p) P) = eqToHom (by rw [p]) := by
  subst p
  ext
  simp

/-- **The assembly of the chase of the proof of [Stacks, Tag 0ATY]**, with variable data: the
chase for the triple (`hΘ`) and the comparison of the rectangle `A + B` with the choice for `f`
and `h ∘ g` (`hΨ`, with comparisons `αE`, `αD` that are identities on the bounded-below part),
read on the bounded-below parts, give the identity of isomorphisms. Every functor is a variable,
so that the identity is checked once, here, and only instantiated afterwards. -/
theorem assembleIso {𝒯 𝒳b 𝒴b 𝒵b 𝒵 𝒲 𝒱 𝒴 𝒰' 𝒰 𝒳 : Type*} [Category 𝒯]
    [Category 𝒳b] [Category 𝒴b] [Category 𝒵b] [Category 𝒵] [Category 𝒲] [Category 𝒱]
    [Category 𝒴] [Category 𝒰'] [Category 𝒰] [Category 𝒳]
    (PT : ObjectProperty 𝒯) (PZ : ObjectProperty 𝒵) (PY : ObjectProperty 𝒴)
    {K : 𝒯 ⥤ 𝒳b} {iX : 𝒳b ⥤ 𝒳} {BC : 𝒯 ⥤ 𝒴b} {iY : 𝒴b ⥤ 𝒴}
    {qU' : 𝒴 ⥤ 𝒰'} {iU' : 𝒰' ⥤ 𝒳} {qU : 𝒴 ⥤ 𝒰} {iU : 𝒰 ⥤ 𝒳} {c : 𝒯 ⥤ 𝒵b} {iZ : 𝒵b ⥤ 𝒵}
    {qW : 𝒵 ⥤ 𝒲} {iW : 𝒲 ⥤ 𝒴} {qV : 𝒵 ⥤ 𝒱} {iV : 𝒱 ⥤ 𝒳} {RQ : 𝒵 ⥤ 𝒱}
    (rowMap : K ⋙ iX ⟶ BC ⋙ iY ⋙ qU' ⋙ iU') (m1 : K ⋙ iX ⟶ BC ⋙ iY ⋙ qU ⋙ iU)
    (mE : BC ⋙ iY ⟶ c ⋙ iZ ⋙ qW ⋙ iW) (m2 : K ⋙ iX ⟶ c ⋙ iZ ⋙ qV ⋙ iV)
    (tr : qV ⋙ iV ⟶ RQ ⋙ iV) (m3 : RQ ⋙ iV ⟶ qW ⋙ iW ⋙ qU' ⋙ iU')
    (αψ : qU' ⋙ iU' ⟶ qU ⋙ iU) (αE : K ⋙ iX ⟶ K ⋙ iX) (αD : BC ⋙ iY ⟶ BC ⋙ iY)
    (hΘ : rowMap ≫ whiskerRight mE (qU' ⋙ iU') = m2 ≫ whiskerLeft (c ⋙ iZ) (tr ≫ m3))
    (hΨ : αE ≫ m1 = rowMap ≫ whiskerLeft (BC ⋙ iY) αψ ≫ whiskerRight αD (qU ⋙ iU))
    (hαE : whiskerLeft PT.ι αE = 𝟙 _) (hαD : whiskerLeft PT.ι αD = 𝟙 _)
    (hY₁ : ∀ T, PY ((PT.ι ⋙ BC ⋙ iY).obj T)) (hZ : ∀ T, PZ ((PT.ι ⋙ c ⋙ iZ).obj T))
    (hW : ∀ M, PY ((PZ.ι ⋙ qW ⋙ iW).obj M))
    (hY₂ : ∀ T, PY ((PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ ⋙ PZ.ι ⋙ qW ⋙ iW).obj T))
    (I₁ : PT.ι ⋙ K ⋙ iX ≅ PY.lift (PT.ι ⋙ BC ⋙ iY) hY₁ ⋙ PY.ι ⋙ qU ⋙ iU)
    (L : PT.ι ⋙ BC ⋙ iY ≅ PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ ⋙ PZ.ι ⋙ qW ⋙ iW)
    (J₁ : PT.ι ⋙ K ⋙ iX ≅ PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ ⋙ PZ.ι ⋙ qV ⋙ iV)
    (A : PZ.ι ⋙ qV ⋙ iV ≅ PZ.ι ⋙ RQ ⋙ iV)
    (J₃ : PZ.ι ⋙ RQ ⋙ iV ≅ PY.lift (PZ.ι ⋙ qW ⋙ iW) hW ⋙ PY.ι ⋙ qU' ⋙ iU')
    (Aψ : PY.ι ⋙ qU' ⋙ iU' ≅ PY.ι ⋙ qU ⋙ iU)
    (h₁ : I₁.hom = whiskerLeft PT.ι m1) (hL : L.hom = whiskerLeft PT.ι mE)
    (h₃ : J₁.hom = whiskerLeft PT.ι m2) (hA : A.hom = whiskerLeft PZ.ι tr)
    (h₅ : J₃.hom = whiskerLeft PZ.ι m3) (hψ : Aψ.hom = whiskerLeft PY.ι αψ) :
    I₁ ≪≫ isoWhiskerRight (liftIsoOf PY hY₁ hY₂ L) (PY.ι ⋙ qU ⋙ iU) =
      J₁ ≪≫ isoWhiskerLeft (PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ) A ≪≫
        isoWhiskerLeft (PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ)
          (J₃ ≪≫ isoWhiskerLeft (PY.lift (PZ.ι ⋙ qW ⋙ iW) hW) Aψ) := by
  have hΨ' := congrArg (whiskerLeft PT.ι) hΨ
  simp only [Functor.whiskerLeft_comp, hαE, Category.id_comp] at hΨ'
  have hD' : whiskerLeft PT.ι (whiskerRight αD (qU ⋙ iU)) = 𝟙 _ := by
    ext T
    have := NatTrans.congr_app hαD T
    simp only [Functor.whiskerLeft_app, NatTrans.id_app] at this
    show (qU ⋙ iU).map (αD.app (PT.ι.obj T)) = 𝟙 _
    rw [this]
    exact (qU ⋙ iU).map_id _
  rw [hD', Category.comp_id] at hΨ'
  have hΘ' := congrArg (whiskerLeft PT.ι) hΘ
  simp only [Functor.whiskerLeft_comp] at hΘ'
  refine Iso.ext (NatTrans.ext (funext fun T => ?_))
  have e1 := NatTrans.congr_app hΨ' T
  have e2 := NatTrans.congr_app hΘ' T
  have nψ := αψ.naturality (mE.app (PT.ι.obj T))
  have i1 := NatTrans.congr_app h₁ T
  have l1 := NatTrans.congr_app hL T
  have j1 := NatTrans.congr_app h₃ T
  have a1 := NatTrans.congr_app hA ((PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ).obj T)
  have j3 := NatTrans.congr_app h₅ ((PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ).obj T)
  have p1 := NatTrans.congr_app hψ
    ((PY.lift (PZ.ι ⋙ qW ⋙ iW) hW).obj ((PZ.lift (PT.ι ⋙ c ⋙ iZ) hZ).obj T))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map] at e1 e2 nψ i1 l1 j1 a1 j3 p1
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, ObjectProperty.ι_map, liftIsoOf_hom_app_hom, i1, l1, j1, a1, j3, p1]
  rw [e1, Category.assoc, ← nψ, ← Category.assoc, e2]
  simp

/-- The cocycle identity of composition isomorphisms, read at an object. -/
private theorem cocycle_iso_app {𝒯 𝒵 𝒴 𝒳 : Type*} [Category 𝒯] [Category 𝒵] [Category 𝒴]
    [Category 𝒳] {Kf : 𝒯 ⥤ 𝒳} {Gh : 𝒯 ⥤ 𝒵} {Gg : 𝒵 ⥤ 𝒴} {Ff : 𝒴 ⥤ 𝒳} (Ggh : 𝒯 ⥤ 𝒴)
    {Ffg : 𝒵 ⥤ 𝒳} {γ1 : Kf ≅ Ggh ⋙ Ff} {γgh : Ggh ≅ Gh ⋙ Gg} {γ2 : Kf ≅ Gh ⋙ Ffg}
    {γ3 : Ffg ≅ Gg ⋙ Ff} (H : γ1 ≪≫ isoWhiskerRight γgh Ff = γ2 ≪≫ isoWhiskerLeft Gh γ3)
    (K : 𝒯) : γ1.hom.app K ≫ Ff.map (γgh.hom.app K) = γ2.hom.app K ≫ γ3.hom.app (Gh.obj K) := by
  simpa using NatTrans.congr_app (congrArg Iso.hom H) K

/-- **Moving the cocycle identity along comparisons**, with variable data: if the four
isomorphisms of the cocycle identity are each compatible with comparisons `A`, `Pa`, … of their
sources and targets, the identity for the first choice gives the identity for the second. -/
theorem cocycleTransport {𝒯 𝒵 𝒴 𝒳 : Type*} [Category 𝒯] [Category 𝒵] [Category 𝒴]
    [Category 𝒳] {Kf Kf' : 𝒯 ⥤ 𝒳} {Gh Gh' : 𝒯 ⥤ 𝒵} {Gg Gg' : 𝒵 ⥤ 𝒴} {Ff Ff' : 𝒴 ⥤ 𝒳}
    {Ggh Ggh' : 𝒯 ⥤ 𝒴} {Ffg Ffg' : 𝒵 ⥤ 𝒳}
    (A : Kf ≅ Kf') (Pc : Gh ≅ Gh') (Pb : Gg ≅ Gg') (Pa : Ff ≅ Ff') (Pgh : Ggh ≅ Ggh')
    (Pfg : Ffg ≅ Ffg')
    (γ1 : Kf ≅ Ggh ⋙ Ff) (γ1' : Kf' ≅ Ggh' ⋙ Ff') (N1 : A ≪≫ γ1' = γ1 ≪≫ NatIso.hcomp Pgh Pa)
    (γgh : Ggh ≅ Gh ⋙ Gg) (γgh' : Ggh' ≅ Gh' ⋙ Gg')
    (Ngh : Pgh ≪≫ γgh' = γgh ≪≫ NatIso.hcomp Pc Pb)
    (γ2 : Kf ≅ Gh ⋙ Ffg) (γ2' : Kf' ≅ Gh' ⋙ Ffg') (N2 : A ≪≫ γ2' = γ2 ≪≫ NatIso.hcomp Pc Pfg)
    (γ3 : Ffg ≅ Gg ⋙ Ff) (γ3' : Ffg' ≅ Gg' ⋙ Ff') (N3 : Pfg ≪≫ γ3' = γ3 ≪≫ NatIso.hcomp Pb Pa)
    (H : γ1 ≪≫ isoWhiskerRight γgh Ff = γ2 ≪≫ isoWhiskerLeft Gh γ3) :
    γ1' ≪≫ isoWhiskerRight γgh' Ff' = γ2' ≪≫ isoWhiskerLeft Gh' γ3' := by
  have e1 : γ1' = A.symm ≪≫ γ1 ≪≫ NatIso.hcomp Pgh Pa := by rw [← N1]; simp
  have egh : γgh' = Pgh.symm ≪≫ γgh ≪≫ NatIso.hcomp Pc Pb := by rw [← Ngh]; simp
  have e2 : γ2' = A.symm ≪≫ γ2 ≪≫ NatIso.hcomp Pc Pfg := by rw [← N2]; simp
  have e3 : γ3' = Pfg.symm ≪≫ γ3 ≪≫ NatIso.hcomp Pb Pa := by rw [← N3]; simp
  subst e1 egh e2 e3
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  have hK := cocycle_iso_app Ggh H K
  have nPa1 := (Pa.hom.naturality (γgh.hom.app K)).symm
  have nPfg := Pfg.inv.naturality (Pc.hom.app K)
  have nγ3 := γ3.hom.naturality (Pc.hom.app K)
  have nPa2 := Pa.hom.naturality (Gg.map (Pc.hom.app K))
  have nPb := Pb.hom.naturality (Pc.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at nPa1 nPfg nγ3 nPa2 nPb
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.hcomp_hom, NatTrans.hcomp_app, Category.assoc, Functor.map_comp]
  rw [← Ff'.map_comp_assoc (Pgh.hom.app K), Iso.hom_inv_id_app, Ff'.map_id, Category.id_comp,
    reassoc_of% nPa1, reassoc_of% hK, reassoc_of% nPfg, Iso.hom_inv_id_app_assoc,
    reassoc_of% nγ3, reassoc_of% nPa2, ← Ff'.map_comp, ← Ff'.map_comp, nPb]

/-- `Stacks.Duality.liftIsoOf` of a horizontal composite. -/
theorem liftIsoOf_hcomp {𝒯 𝒵 𝒴 : Type*} [Category 𝒯] [Category 𝒵] [Category 𝒴]
    (P : ObjectProperty 𝒴) {G G' : 𝒯 ⥤ 𝒵} {H H' : 𝒵 ⥤ 𝒴} (b : G ≅ G') (c : H ≅ H')
    (hH : ∀ K, P (H.obj K)) (hH' : ∀ K, P (H'.obj K)) (h₁ : ∀ K, P ((G ⋙ H).obj K))
    (h₂ : ∀ K, P ((G' ⋙ H').obj K)) :
    liftIsoOf P h₁ h₂ (NatIso.hcomp b c) = NatIso.hcomp b (liftIsoOf P hH hH' c) := by
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  simp [liftIsoOf]

end NatShapes

/-! ### The unit of a pseudofunctor from its compositor -/

section Units

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]

/-- **The unit determined by a compositor.** For an endofunctor `F` with an isomorphism
`μ : F ≅ F ⋙ F` and some isomorphism `ε : F ≅ 𝟭`, the isomorphism `F ≅ 𝟭` whose component at
`F K` is the inverse of the component of `μ` at `K`. -/
def unitOf {F : 𝒜 ⥤ 𝒜} (μ : F ≅ F ⋙ F) (ε : F ≅ 𝟭 𝒜) : F ≅ 𝟭 𝒜 :=
  (Functor.leftUnitor F).symm ≪≫ isoWhiskerRight ε.symm F ≪≫ μ.symm ≪≫ ε

/-- For an isomorphism `u : F ≅ 𝟭`, `F u = u F`. -/
theorem map_hom_app_of_iso_id {F : 𝒜 ⥤ 𝒜} (u : F ≅ 𝟭 𝒜) (K : 𝒜) :
    F.map (u.hom.app K) = u.hom.app (F.obj K) := by
  have n := u.hom.naturality (u.hom.app K)
  simp only [Functor.id_map] at n
  exact (cancel_mono (u.hom.app K)).1 n

/-- The component of `unitOf μ ε` at `F K` is the component of `μ⁻¹` at `K`. -/
theorem unitOf_hom_app_obj {F : 𝒜 ⥤ 𝒜} (μ : F ≅ F ⋙ F) (ε : F ≅ 𝟭 𝒜) (K : 𝒜) :
    (unitOf μ ε).hom.app (F.obj K) = μ.inv.app K := by
  have hε : ε.inv.app (F.obj K) = F.map (ε.inv.app K) := by
    rw [← cancel_mono (ε.hom.app (F.obj K)), Iso.inv_hom_id_app,
      ← map_hom_app_of_iso_id ε K, ← F.map_comp, Iso.inv_hom_id_app, F.map_id]
    rfl
  have n := μ.inv.naturality (ε.hom.app K)
  simp only [Functor.comp_map] at n
  simp only [unitOf, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp]
  rw [hε, ← map_hom_app_of_iso_id ε K, ← n, ← Functor.map_comp_assoc, ← F.map_comp,
    Iso.inv_hom_id_app]
  simp

/-- **The left unit law from the cocycle identity.** -/
theorem unitOf_left {F : 𝒜 ⥤ 𝒜} (μ : F ≅ F ⋙ F) (ε : F ≅ 𝟭 𝒜) {Φ : 𝒜 ⥤ ℬ} (l : Φ ≅ F ⋙ Φ)
    (h : ∀ K, l.hom.app K ≫ Φ.map (μ.hom.app K) = l.hom.app K ≫ l.hom.app (F.obj K))
    (K : 𝒜) : l.hom.app K ≫ Φ.map ((unitOf μ ε).hom.app K) = 𝟙 _ := by
  have h1 : Φ.map (μ.hom.app K) = l.hom.app (F.obj K) := (cancel_epi (l.hom.app K)).1 (h K)
  have hF : F.map ((unitOf μ ε).hom.app K) = μ.inv.app K := by
    rw [map_hom_app_of_iso_id, unitOf_hom_app_obj]
  have n := l.hom.naturality ((unitOf μ ε).hom.app K)
  simp only [Functor.comp_map, hF, Functor.id_obj] at n
  have h2 : Φ.map ((unitOf μ ε).hom.app K) ≫ l.hom.app K = 𝟙 _ := by
    rw [n, ← h1, ← Φ.map_comp, Iso.hom_inv_id_app, Φ.map_id]
  rw [← cancel_mono (l.hom.app K), Category.assoc, h2]
  simp

/-- **The right unit law from the cocycle identity.** -/
theorem unitOf_right {G : ℬ ⥤ ℬ} (μ : G ≅ G ⋙ G) (ε : G ≅ 𝟭 ℬ) {Ψ : 𝒜 ⥤ ℬ} (r : Ψ ≅ Ψ ⋙ G)
    (h : ∀ K, r.hom.app K ≫ G.map (r.hom.app K) = r.hom.app K ≫ μ.hom.app (Ψ.obj K))
    (K : 𝒜) : r.hom.app K ≫ (unitOf μ ε).hom.app (Ψ.obj K) = 𝟙 _ := by
  have h1 : G.map (r.hom.app K) = μ.hom.app (Ψ.obj K) := (cancel_epi (r.hom.app K)).1 (h K)
  have n := (unitOf μ ε).hom.naturality (r.hom.app K)
  simp only [Functor.id_map, Functor.comp_obj] at n
  rw [unitOf_hom_app_obj, h1, Iso.hom_inv_id_app] at n
  rw [← cancel_mono (r.hom.app K), Category.assoc, ← n]
  simp

end Units

/-! ### Reading the axioms of a pseudofunctor into `Cat` on components -/

section CatLaws

universe v w

open CategoryTheory.Bicategory

variable {𝒯 𝒵 𝒴 𝒳 : Type w} [Category.{v} 𝒯] [Category.{v} 𝒵] [Category.{v} 𝒴]
  [Category.{v} 𝒳]

/-- **The associativity axiom of a pseudofunctor into `Cat`** for compositors lifted to a full
subcategory, from the cocycle identity of the compositors. -/
theorem catAssoc (P : ObjectProperty 𝒳) {Gh : 𝒯 ⥤ 𝒵} {Gg : 𝒵 ⥤ 𝒴} {Ggh : 𝒯 ⥤ 𝒴}
    {Ff : 𝒴 ⥤ 𝒳} {Ffg : 𝒵 ⥤ 𝒳} {Kf : 𝒯 ⥤ 𝒳} (hF : ∀ K, P (Ff.obj K))
    (hFfg : ∀ K, P (Ffg.obj K)) (hK : ∀ K, P (Kf.obj K))
    (γ1 : Kf ≅ Ggh ⋙ Ff) (γgh : Ggh ≅ Gh ⋙ Gg) (γ2 : Kf ≅ Gh ⋙ Ffg) (γ3 : Ffg ≅ Gg ⋙ Ff)
    (H : γ1 ≪≫ isoWhiskerRight γgh Ff = γ2 ≪≫ isoWhiskerLeft Gh γ3) :
    (Cat.Hom.isoMk (liftIsoOf P hK (fun _ => hF _) γ1)).hom ≫
        (Cat.Hom.isoMk γgh).hom ▷ (P.lift Ff hF).toCatHom ≫
          (α_ Gh.toCatHom Gg.toCatHom (P.lift Ff hF).toCatHom).hom ≫
            Gh.toCatHom ◁ (Cat.Hom.isoMk (liftIsoOf P hFfg (fun _ => hF _) γ3)).inv ≫
              (Cat.Hom.isoMk (liftIsoOf P hK (fun _ => hFfg _) γ2)).inv = 𝟙 _ := by
  refine Cat.Hom₂.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  have h := cocycle_iso_app Ggh H K
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app, Cat.Hom.isoMk_hom,
    Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.id_app]
  show γ1.hom.app K ≫ Ff.map (γgh.hom.app K) ≫ 𝟙 _ ≫ γ3.inv.app (Gh.obj K) ≫
    γ2.inv.app K = 𝟙 _
  rw [Category.id_comp, reassoc_of% h]
  simp

/-- **The left unit axiom of a pseudofunctor into `Cat`** for the unit
`Stacks.Duality.unitOf`, from the cocycle identity at `(f, 𝟙, 𝟙)`. -/
theorem catLeft (P : ObjectProperty 𝒳) {F : 𝒴 ⥤ 𝒴} {Φ₀ : 𝒴 ⥤ 𝒳} (hΦ : ∀ K, P (Φ₀.obj K))
    (μ : F ≅ F ⋙ F) (eU : F ≅ 𝟭 𝒴) (l₀ : Φ₀ ≅ F ⋙ Φ₀)
    (H : l₀ ≪≫ isoWhiskerRight μ Φ₀ = l₀ ≪≫ isoWhiskerLeft F l₀) :
    (Cat.Hom.isoMk (liftIsoOf P hΦ (F₂ := F ⋙ Φ₀) (fun _ => hΦ _) l₀)).hom ≫
        (Cat.Hom.isoMk (unitOf μ eU)).hom ▷ (P.lift Φ₀ hΦ).toCatHom ≫
          (λ_ (P.lift Φ₀ hΦ).toCatHom).hom = 𝟙 _ := by
  refine Cat.Hom₂.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  have h := cocycle_iso_app _ H
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.Hom.isoMk_hom,
    NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.id_app]
  show l₀.hom.app K ≫ Φ₀.map ((unitOf μ eU).hom.app K) ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  exact unitOf_left μ eU l₀ h K

/-- **The right unit axiom of a pseudofunctor into `Cat`** for the unit
`Stacks.Duality.unitOf`, from the cocycle identity at `(𝟙, 𝟙, f)`. -/
theorem catRight (P : ObjectProperty 𝒳) {Ψ₀ : 𝒴 ⥤ 𝒳} {G₀ : P.FullSubcategory ⥤ 𝒳}
    (hΨ : ∀ K, P (Ψ₀.obj K)) (hG : ∀ K, P (G₀.obj K))
    (μ₀ : G₀ ≅ P.lift G₀ hG ⋙ G₀) (eU : P.lift G₀ hG ≅ 𝟭 _) (r₀ : Ψ₀ ≅ P.lift Ψ₀ hΨ ⋙ G₀)
    (H : r₀ ≪≫ isoWhiskerRight (liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun _ => hG _) r₀) G₀ =
      r₀ ≪≫ isoWhiskerLeft (P.lift Ψ₀ hΨ) μ₀) :
    (Cat.Hom.isoMk (liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun _ => hG _) r₀)).hom ≫
        (P.lift Ψ₀ hΨ).toCatHom ◁
          (Cat.Hom.isoMk (unitOf (liftIsoOf P hG (F₂ := P.lift G₀ hG ⋙ G₀)
            (fun _ => hG _) μ₀) eU)).hom ≫
          (ρ_ (P.lift Ψ₀ hΨ).toCatHom).hom = 𝟙 _ := by
  refine Cat.Hom₂.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  have h : ∀ K, (liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun K => hG _) r₀).hom.app K ≫
      (P.lift G₀ hG).map ((liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun K => hG _) r₀).hom.app K) =
      (liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun K => hG _) r₀).hom.app K ≫
        (liftIsoOf P hG (F₂ := P.lift G₀ hG ⋙ G₀) (fun K => hG _) μ₀).hom.app
          ((P.lift Ψ₀ hΨ).obj K) := fun K =>
    ObjectProperty.hom_ext _ (by simpa using cocycle_iso_app (Gg := P.lift G₀ hG) _ H K)
  have hr := unitOf_right (liftIsoOf P hG (F₂ := P.lift G₀ hG ⋙ G₀) (fun K => hG _) μ₀) eU
    (liftIsoOf P hΨ (F₂ := P.lift Ψ₀ hΨ ⋙ G₀) (fun K => hG _) r₀) h K
  have hr' := congrArg (fun x => x.hom) hr
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    liftIsoOf_hom_app_hom] at hr'
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.Hom.isoMk_hom,
    NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.id_app]
  show r₀.hom.app K ≫ ((unitOf (liftIsoOf P hG (F₂ := P.lift G₀ hG ⋙ G₀)
    (fun K => hG _) μ₀) eU).hom.app
    ((P.lift Ψ₀ hΨ).obj K)).hom ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  exact hr'

end CatLaws

end Chase

end Stacks.Duality

end
