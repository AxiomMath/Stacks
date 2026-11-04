module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# Morphisms over a cover by two monomorphisms

Let `F` be a pseudofunctor from `Cᵒᵖ` to categories, `i₁ : X₁ ⟶ S` and `i₂ : X₂ ⟶ S` two
monomorphisms with pullback `X₁₂`, and suppose that `F.toDescentData` is fully faithful for the
family `{i₁, i₂}` (as it is when `F` is a prestack and the family covers `S`). Let `M`, `N` be
objects over `S`. If every morphism `j₂^* i₂^* M ⟶ j₂^* i₂^* N` over `X₁₂` comes from a morphism
`i₂^* M ⟶ i₂^* N` over `X₂`, then every morphism `i₁^* M ⟶ i₁^* N` over `X₁` comes from a
morphism `M ⟶ N` over `S`.

Indeed a morphism over `X₁` extends to the second member of the cover by the hypothesis, and the
compatibilities of descent data are only to be checked over the chosen pullbacks of the pairs of
members (`CategoryTheory.Pseudofunctor.DescentData'`): over `X₁ ×_S X₁` and `X₂ ×_S X₂`, which
are `X₁` and `X₂` themselves since the members are monomorphisms, nothing is to be checked, and
over `X₁ ×_S X₂ = X₁₂` the condition is the defining property of the extension.

This is the gluing step "a h covering given by a pair of closed immersions" of the proof of
Stacks Tag 0EXH.

## Main results

* `CategoryTheory.Pseudofunctor.exists_map_eq_of_monoPair`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.LocallyDiscreteOpToCat

universe t v' u' v u

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S X₁ X₂ X₁₂ : C} (i₁ : X₁ ⟶ S) (i₂ : X₂ ⟶ S) (j₁ : X₁₂ ⟶ X₁) (j₂ : X₁₂ ⟶ X₂)

/-- The members of the family `{i₁, i₂}`, indexed by `Bool`. -/
abbrev monoPairObj (b : Bool) : C := Bool.rec X₁ X₂ b

/-- The family `{i₁, i₂}`, indexed by `Bool`. -/
abbrev monoPairHom : ∀ b : Bool, monoPairObj (X₁ := X₁) (X₂ := X₂) b ⟶ S :=
  fun b ↦ Bool.rec (motive := fun b ↦ monoPairObj (X₁ := X₁) (X₂ := X₂) b ⟶ S) i₁ i₂ b

variable {i₁ i₂ j₁ j₂}

/-- The diagonal chosen pullback of a monomorphism with itself: the source with the identity
maps. -/
def ChosenPullback.diagOfMono {X : C} (i : X ⟶ S) [Mono i] : ChosenPullback i i where
  pullback := X
  p₁ := 𝟙 X
  p₂ := 𝟙 X
  condition := rfl
  isLimit := (IsKernelPair.id_of_mono i).isLimit

/-- Chosen pullbacks of the pairs of members of the family `{i₁, i₂}`: the diagonal ones are the
members themselves, the off-diagonal ones the given pullback `X₁₂`. -/
def monoPairChosenPullback [Mono i₁] [Mono i₂] (hsq : IsPullback j₁ j₂ i₁ i₂) :
    ∀ a b : Bool, ChosenPullback (monoPairHom i₁ i₂ a) (monoPairHom i₁ i₂ b)
  | false, false => ChosenPullback.diagOfMono i₁
  | true, true => ChosenPullback.diagOfMono i₂
  | false, true => ⟨X₁₂, j₁, j₂, hsq.w, hsq.isLimit, _, rfl⟩
  | true, false => ⟨X₁₂, j₂, j₁, hsq.w.symm, hsq.flip.isLimit, _, rfl⟩

/-- Chosen threefold pullbacks for the family `{i₁, i₂}`. -/
noncomputable def monoPairChosenPullback₃ [HasPullbacks C] [Mono i₁] [Mono i₂]
    (hsq : IsPullback j₁ j₂ i₁ i₂) (a b c : Bool) :
    ChosenPullback₃ (monoPairChosenPullback hsq a b) (monoPairChosenPullback hsq b c)
      (monoPairChosenPullback hsq a c) :=
  ChosenPullback₃.ofHasPullbacks _ _ _

/-- The comparison isomorphism of a descent datum is inverted by swapping its two sections. -/
private theorem hom_swap_eq_inv {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (D : F.DescentData f) {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₂ f₁ hf₂ hf₁ = inv (D.hom q f₁ f₂ hf₁ hf₂) :=
  IsIso.eq_inv_of_hom_inv_id ((D.hom_comp q f₁ f₂ f₁ hf₁ hf₂ hf₁).trans (D.hom_self _ _ hf₁))

/-- A morphism of the `i`-th objects of two descent data commutes with the identity comparison. -/
private theorem comm_of_hom_self {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (D D' : F.DescentData f) {i : ι} (x : D.obj i ⟶ D'.obj i) (q : X i ⟶ S)
    (hq : 𝟙 (X i) ≫ f i = q) :
    (F.map (𝟙 (X i)).op.toLoc).toFunctor.map x ≫ D'.hom q (𝟙 _) (𝟙 _) hq hq =
      D.hom q (𝟙 _) (𝟙 _) hq hq ≫ (F.map (𝟙 (X i)).op.toLoc).toFunctor.map x := by
  rw [D.hom_self q _ hq, D'.hom_self q _ hq]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Morphisms over a cover by two monomorphisms.** If `F.toDescentData` is fully faithful for
the family `{i₁, i₂}` of monomorphisms, and pullback to `X₁₂` is surjective on morphisms
`i₂^* M ⟶ i₂^* N`, then every morphism `i₁^* M ⟶ i₁^* N` is the pullback of a morphism
`M ⟶ N`. -/
theorem exists_map_eq_of_monoPair [HasPullbacks C] [Mono i₁] [Mono i₂]
    (hsq : IsPullback j₁ j₂ i₁ i₂)
    (hff : (F.toDescentData (monoPairHom i₁ i₂)).FullyFaithful)
    {M N : F.obj (.mk (op S))}
    (hsurj : Function.Surjective
      (fun φ : (F.map i₂.op.toLoc).toFunctor.obj M ⟶ (F.map i₂.op.toLoc).toFunctor.obj N ↦
        (F.map j₂.op.toLoc).toFunctor.map φ))
    (x₁ : (F.map i₁.op.toLoc).toFunctor.obj M ⟶ (F.map i₁.op.toLoc).toFunctor.obj N) :
    ∃ φ : M ⟶ N, (F.map i₁.op.toLoc).toFunctor.map φ = x₁ := by
  let DM := (F.toDescentData (monoPairHom i₁ i₂)).obj M
  let DN := (F.toDescentData (monoPairHom i₁ i₂)).obj N
  have hw : j₂ ≫ i₂ = j₁ ≫ i₁ := hsq.w.symm
  let τM : (F.map j₁.op.toLoc).toFunctor.obj ((F.map i₁.op.toLoc).toFunctor.obj M) ⟶
      (F.map j₂.op.toLoc).toFunctor.obj ((F.map i₂.op.toLoc).toFunctor.obj M) :=
    DM.hom (j₁ ≫ i₁) (i₁ := false) (i₂ := true) j₁ j₂ rfl hw
  let τN : (F.map j₁.op.toLoc).toFunctor.obj ((F.map i₁.op.toLoc).toFunctor.obj N) ⟶
      (F.map j₂.op.toLoc).toFunctor.obj ((F.map i₂.op.toLoc).toFunctor.obj N) :=
    DN.hom (j₁ ≫ i₁) (i₁ := false) (i₂ := true) j₁ j₂ rfl hw
  have : IsIso τM := inferInstanceAs (IsIso (DM.hom _ _ _ _ _))
  obtain ⟨x₂, hx₂⟩ := hsurj (inv τM ≫ (F.map j₁.op.toLoc).toFunctor.map x₁ ≫ τN)
  have hx₂' : (F.map j₂.op.toLoc).toFunctor.map x₂ =
      inv τM ≫ (F.map j₁.op.toLoc).toFunctor.map x₁ ≫ τN := hx₂
  have hcomm₁₂ : (F.map j₁.op.toLoc).toFunctor.map x₁ ≫ τN =
      τM ≫ (F.map j₂.op.toLoc).toFunctor.map x₂ := by
    rw [hx₂', IsIso.hom_inv_id_assoc]
  -- the inverse comparison over `X₁₂`
  have : IsIso τN := inferInstanceAs (IsIso (DN.hom _ _ _ _ _))
  have hswap : ∀ D : F.DescentData (monoPairHom i₁ i₂),
      D.hom (j₂ ≫ i₂) (i₁ := true) (i₂ := false) j₂ j₁ rfl hsq.w =
        inv (D.hom (j₁ ≫ i₁) (i₁ := false) (i₂ := true) j₁ j₂ rfl hw) := fun D ↦
    (by congr 1 : _ = D.hom (j₁ ≫ i₁) (i₁ := true) (i₂ := false) j₂ j₁ hw rfl).trans
      (hom_swap_eq_inv F D (j₁ ≫ i₁) (i₁ := false) (i₂ := true) j₁ j₂ rfl hw)
  -- the morphism of descent data relative to the chosen pullbacks
  let sq := monoPairChosenPullback hsq
  let sq₃ := monoPairChosenPullback₃ hsq
  let φ' : DescentData'.ofDescentData sq sq₃ DM ⟶ DescentData'.ofDescentData sq sq₃ DN :=
    { hom := fun b ↦ Bool.rec (motive := fun b ↦ DM.obj b ⟶ DN.obj b) x₁ x₂ b
      comm := by
        intro a b
        cases a <;> cases b
        · exact comm_of_hom_self F DM DN (i := false) x₁ _ rfl
        · exact hcomm₁₂
        · change (F.map j₂.op.toLoc).toFunctor.map x₂ ≫
              DN.hom (j₂ ≫ i₂) (i₁ := true) (i₂ := false) j₂ j₁ rfl hsq.w =
            DM.hom (j₂ ≫ i₂) (i₁ := true) (i₂ := false) j₂ j₁ rfl hsq.w ≫
              (F.map j₁.op.toLoc).toFunctor.map x₁
          have key : (F.map j₂.op.toLoc).toFunctor.map x₂ ≫ inv τN =
              inv τM ≫ (F.map j₁.op.toLoc).toFunctor.map x₁ := by
            rw [hx₂']
            simp
          rw [hswap, hswap]
          exact key
        · exact comm_of_hom_self F DM DN (i := true) x₂ _ rfl }
  let φ : DM ⟶ DN :=
    { hom := φ'.hom
      comm := fun Y q a b f₁ f₂ hf₁ hf₂ ↦ by
        have h := DescentData'.comm φ' q f₁ f₂ hf₁ hf₂
        rwa [DescentData'.pullHom'_ofDescentData_hom,
          DescentData'.pullHom'_ofDescentData_hom] at h }
  exact ⟨hff.preimage φ, congrArg (fun ψ : DM ⟶ DN ↦ ψ.hom false) (hff.map_preimage φ)⟩

/-- **Pullback is surjective on morphisms between objects pulled back from a scheme along
which, composed with the pullback, the transition functor is full.** Let `a : U ⟶ V`,
`j : U' ⟶ U`, with `F` full along `j ≫ a`. Then every morphism between the pullbacks along `j`
of two objects of `F U` isomorphic to pullbacks along `a` is the pullback of a morphism. -/
theorem surjective_map_of_full {U' U V : C} (j : U' ⟶ U) (a : U ⟶ V) (ja : U' ⟶ V)
    (hja : j ≫ a = ja) [(F.map ja.op.toLoc).toFunctor.Full] {P Q : F.obj (.mk (op V))}
    {M' N' : F.obj (.mk (op U))} (eM : M' ≅ (F.map a.op.toLoc).toFunctor.obj P)
    (eN : N' ≅ (F.map a.op.toLoc).toFunctor.obj Q) :
    Function.Surjective (fun φ : M' ⟶ N' ↦ (F.map j.op.toLoc).toFunctor.map φ) := by
  intro y
  subst hja
  let e : (F.map (j ≫ a).op.toLoc).toFunctor ≅
      (F.map a.op.toLoc).toFunctor ⋙ (F.map j.op.toLoc).toFunctor :=
    Cat.Hom.toNatIso (F.mapComp' a.op.toLoc j.op.toLoc (j ≫ a).op.toLoc rfl)
  have : ((F.map a.op.toLoc).toFunctor ⋙ (F.map j.op.toLoc).toFunctor).Full :=
    Functor.Full.of_iso e
  let Fj := (F.map j.op.toLoc).toFunctor
  obtain ⟨z, hz⟩ := ((F.map a.op.toLoc).toFunctor ⋙ Fj).map_surjective
    (Fj.map eM.inv ≫ y ≫ Fj.map eN.hom)
  refine ⟨eM.hom ≫ (F.map a.op.toLoc).toFunctor.map z ≫ eN.inv, ?_⟩
  have hz' : Fj.map ((F.map a.op.toLoc).toFunctor.map z) = Fj.map eM.inv ≫ y ≫ Fj.map eN.hom := hz
  change Fj.map (eM.hom ≫ (F.map a.op.toLoc).toFunctor.map z ≫ eN.inv) = y
  rw [Fj.map_comp, Fj.map_comp, hz']
  simp only [Category.assoc, ← Fj.map_comp, eN.hom_inv_id, Fj.map_id,
    ← Fj.map_comp_assoc, eM.hom_inv_id, Category.id_comp]
  exact Category.comp_id y

end CategoryTheory.Pseudofunctor

end
