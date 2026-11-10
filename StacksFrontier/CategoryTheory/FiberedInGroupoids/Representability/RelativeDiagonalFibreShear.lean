module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct

/-!
# The shear map of the fibre of a relative diagonal

Let `F : X ⥤ 𝒴` be a 1-morphism of categories over `𝒞`, let `Y = (x₁, x₂, α)` be a point of
`X ×_{F, 𝒴, F} X` over `𝒯` and write

`R = Isom^α(x₁, x₂)`

for the presheaf on `𝒯` of vertical morphisms `x₁ ⟶ x₂` lying over `α`
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf`), which is the
fibre of the relative diagonal `Δ_F` at `Y`. Composing `Y₂ = x₂` with `Δ_F` gives a second point
`(x₂, x₂, id)` of `X ×_{F, 𝒴, F} X`, whose own fibre

`G = Isom^{id}(x₂, x₂)`

is the presheaf of vertical automorphisms of `x₂` killed by `F`. This file writes down the
**shear map**

`R ×_𝒯 R ⟶ G`, `(m, m') ↦ m'⁻¹ ≫ m`,

and proves that together with the second projection it exhibits `R ×_𝒯 R` as the fibre product
`G ×_𝒯 R`: over a fixed `m'` the operation `m ↦ m'⁻¹ ≫ m` is a bijection from the sections of
`R` to the sections of `G`, with inverse `b ↦ m' ≫ b`. So the second projection
`R ×_𝒯 R ⟶ R` is a base change of the structural morphism `G ⟶ 𝒯`.

This is the one step a *pseudo-torsor* would otherwise be needed for: `R` is a pseudo-torsor
under `G`, and what the statements below record is the single consequence of that fact which the
converse directions of parts (4) and (5) of **Stacks 0CL0** use — the triviality of the torsor
over itself — with no group object, no action and no representability hypothesis anywhere.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.diagPoint`: the point
  `(x₂, x₂, id)`.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.shear` and
  `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.unshear`: the two operations on
  sections.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.shearMap`: the shear as a morphism
  of presheaves out of the explicit fibre product.

## Main results

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.isPullback_shearMap`: the shear map
  and the second projection form a cartesian square over the structural morphisms of `G` and
  `R`.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.arrowIsoPullbackSndShear`: hence the
  second projection of `R ×_𝒯 R` is, as an arrow, the base change of `G ⟶ 𝒯` along `R ⟶ 𝒯`.

## Implementation notes

`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.diagPoint` is `Y₂ ⋙ Δ_F`, and the
three facts that make it usable are definitional: its two components are `Y₂` itself
(`CategoryTheory.TwoFibreProductOver.diagonal_comp_fst` and `...diagonal_comp_snd` are `rfl`),
its comparison isomorphism is the identity, and it is a point over `𝒯`
(`CategoryTheory.TwoFibreProductOver.diagonal_comp_structureFunctor` is `rfl`, which is why
`diagPoint_comp_relProdP` is `h2'` of the given point). The three projections `fst`, `snd` and
`diagonal` are made `implicit_reducible` locally, as in the two files this one extends, so that
the composites typecheck at the transparency the elaborator uses for implicit arguments.

A section of `relVertHomPresheaf` is a vertical morphism of `X`, which is invertible because `p`
is fibred in groupoids
(`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.isIso`); the inverse is taken with the
instance supplied by hand rather than by search, so that no `IsIso` side condition leaks into a
statement. Proof irrelevance makes the choice immaterial.

The fibre product is the explicit
`CategoryTheory.Presheaf.fibreProduct`, whose sections are literally pairs, because the shear is
defined on pairs; the comparison with `CategoryTheory.Limits.pullback` is made once, in
`arrowIsoPullbackSndShear`, which is the form a property of morphisms of algebraic spaces is
transported along.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ u₄

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₃} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
  {Y : 𝒯 ⥤ RelProd p q F}

/-- The point `(x₂, x₂, id)` of `X ×_{F, 𝒴, F} X` attached to the second component of a point
`Y = (x₁, x₂, α)`: the second component composed with the relative diagonal. -/
abbrev diagPoint (Y : 𝒯 ⥤ RelProd p q F) (hF : F ⋙ q = p) : 𝒯 ⥤ RelProd p q F :=
  Y₂' Y ⋙ RelDiag hF

/-- The diagonal point of a point over `𝒯` is again a point over `𝒯`: the relative diagonal is
strictly over `𝒞`, so this is the second component's own compatibility. -/
lemma diagPoint_comp_relProdP (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    diagPoint Y hF ⋙ RelProdP p q F = p𝒯 :=
  h2' hY

namespace RelVertHom

/-- The inverse of a section of `relVertHomPresheaf`, as a morphism of `X`: a vertical morphism
of a category fibred in groupoids is invertible. -/
noncomputable def invHom (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    (Y₂' Y).obj a ⟶ (Y₁' Y).obj a :=
  @CategoryTheory.inv _ _ _ _ m.1.1 (VertHom.isIso hp m.1)

/-- A section of `relVertHomPresheaf` followed by its inverse is the identity. -/
@[simp] lemma comp_invHom (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    m.1.1 ≫ invHom hp m = 𝟙 _ := by
  have := VertHom.isIso hp m.1
  exact IsIso.hom_inv_id m.1.1

/-- The inverse of a section of `relVertHomPresheaf` followed by the section is the identity. -/
@[simp] lemma invHom_comp (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    invHom hp m ≫ m.1.1 = 𝟙 _ := by
  have := VertHom.isIso hp m.1
  exact IsIso.inv_hom_id m.1.1

/-- The inverse of a section of `relVertHomPresheaf` is again vertical. -/
lemma isHomLift_invHom (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    p.IsHomLift (𝟙 (p𝒯.obj a)) (invHom hp m) := by
  have := VertHom.isIso hp m.1
  exact @IsHomLift.lift_id_inv _ _ _ _ p _ _ _ (asIso m.1.1) m.1.2

/-- The image under `F` of the inverse of a section cancels the image of the section. -/
lemma map_invHom_comp (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    F.map (invHom hp m) ≫ F.map m.1.1 = 𝟙 (F.obj ((Y₂' Y).obj a)) := by
  rw [← F.map_comp, invHom_comp, F.map_id]

end RelVertHom

/-- **The shear of two sections.** For two vertical morphisms `m, m' : x₁ ⟶ x₂` lying over the
comparison isomorphism `α` of `Y`, the composite `m'⁻¹ ≫ m` is a vertical automorphism of `x₂`
whose image under `F` is the identity, i.e. a section of the fibre of the relative diagonal at
the diagonal point `(x₂, x₂, id)`. -/
noncomputable def shear (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) {a : 𝒯}
    (m m' : RelVertHom p𝒯 Y a) :
    RelVertHom p𝒯 (diagPoint Y hF) a :=
  ⟨⟨RelVertHom.invHom hp m' ≫ m.1.1,
      Functor.isHomLift_comp_of_isHomLift_id p _ _ (𝟙 (p𝒯.obj a))
        (RelVertHom.isHomLift_invHom hp m') m.1.2⟩,
    by
      have hmm' : F.map m.1.1 = F.map m'.1.1 := m.2.trans m'.2.symm
      have key : F.map (RelVertHom.invHom hp m' ≫ m.1.1)
          = 𝟙 (F.obj ((Y₂' Y).obj a)) := by
        rw [F.map_comp, hmm', RelVertHom.map_invHom_comp hp m']
      exact key⟩

/-- The underlying morphism of the shear of `m` by `m'` is `m'⁻¹ ≫ m`. -/
@[simp] lemma shear_coe (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) {a : 𝒯}
    (m m' : RelVertHom p𝒯 Y a) :
    (shear hp hF m m').1.1 = RelVertHom.invHom hp m' ≫ m.1.1 := rfl

/-- The shear of `m` by `m'`, composed with `m'` on the left, is `m` again. -/
lemma comp_shear (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) {a : 𝒯}
    (m m' : RelVertHom p𝒯 Y a) :
    m'.1.1 ≫ (shear hp hF m m').1.1 = m.1.1 := by
  rw [shear_coe, ← Category.assoc, RelVertHom.comp_invHom, Category.id_comp]

/-- **The inverse of the shear.** Postcomposing a vertical automorphism of `x₂` killed by `F`
with a section `m'` of `Isom^α(x₁, x₂)` gives another section of `Isom^α(x₁, x₂)`. -/
noncomputable def unshear (hF : F ⋙ q = p) {a : 𝒯} (b : RelVertHom p𝒯 (diagPoint Y hF) a)
    (m' : RelVertHom p𝒯 Y a) :
    RelVertHom p𝒯 Y a :=
  ⟨⟨m'.1.1 ≫ b.1.1,
      Functor.isHomLift_comp_of_isHomLift_id p _ _ (𝟙 (p𝒯.obj a)) m'.1.2 b.1.2⟩,
    by
      have key : F.map (m'.1.1 ≫ b.1.1) = (Y.obj a).iso.hom := by
        rw [F.map_comp, m'.2]
        have hb : F.map b.1.1 = 𝟙 (F.obj ((Y₂' Y).obj a)) := b.2
        rw [hb, Category.comp_id]
      exact key⟩

/-- The underlying morphism of the unshear of `b` by `m'` is `m' ≫ b`. -/
@[simp] lemma unshear_coe (hF : F ⋙ q = p) {a : 𝒯} (b : RelVertHom p𝒯 (diagPoint Y hF) a)
    (m' : RelVertHom p𝒯 Y a) :
    (unshear hF b m').1.1 = m'.1.1 ≫ b.1.1 := rfl

/-- Shearing the unshear of `b` by `m'` returns `b`. -/
lemma shear_unshear (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) {a : 𝒯}
    (b : RelVertHom p𝒯 (diagPoint Y hF) a)
    (m' : RelVertHom p𝒯 Y a) :
    shear hp hF (unshear hF b m') m' = b := by
  have := VertHom.isIso hp m'.1
  refine RelVertHom.ext ?_
  have h := comp_shear hp hF (unshear hF b m') m'
  rw [unshear_coe] at h
  exact (cancel_epi m'.1.1).mp h

/-- Unshearing the shear of `m` by `m'` returns `m`. -/
lemma unshear_shear (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) {a : 𝒯}
    (m m' : RelVertHom p𝒯 Y a) :
    unshear hF (shear hp hF m m') m' = m :=
  RelVertHom.ext ((unshear_coe hF _ m').trans (comp_shear hp hF m m'))

/-- **The shear is compatible with restriction.** Both sides are vertical fill-ins of the same
square against `Y₂ h`, which is strongly cartesian because `p` is fibred in groupoids. -/
lemma shear_restrict (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a' a : 𝒯} (h : a' ⟶ a)
    (m m' : RelVertHom p𝒯 Y a) :
    shear hp hF (RelVertHom.restrict hq hp hY hF h m) (RelVertHom.restrict hq hp hY hF h m')
      = RelVertHom.restrict hq hp (diagPoint_comp_relProdP hY hF) hF h
          (shear hp hF m m') := by
  refine RelVertHom.restrict_uniq hq hp (diagPoint_comp_relProdP hY hF) hF h _ _ ?_
  have hfac : ∀ n : RelVertHom p𝒯 Y a, (RelVertHom.restrict hq hp hY hF h n).1.1 ≫ (Y₂' Y).map h
      = (Y₁' Y).map h ≫ n.1.1 := fun n =>
    VertHom.restrict_fac hp (h1' hY) (h2' hY) h n.1
  have := VertHom.isIso hp (RelVertHom.restrict hq hp hY hF h m').1
  have key : RelVertHom.invHom hp (RelVertHom.restrict hq hp hY hF h m') ≫ (Y₁' Y).map h
      = (Y₂' Y).map h ≫ RelVertHom.invHom hp m' := by
    refine (cancel_epi (RelVertHom.restrict hq hp hY hF h m').1.1).mp ?_
    rw [← Category.assoc, RelVertHom.comp_invHom, Category.id_comp, ← Category.assoc, hfac,
      Category.assoc, RelVertHom.comp_invHom, Category.comp_id]
  change (RelVertHom.invHom hp (RelVertHom.restrict hq hp hY hF h m') ≫
      (RelVertHom.restrict hq hp hY hF h m).1.1) ≫ (Y₂' Y).map h
    = (Y₂' Y).map h ≫ (RelVertHom.invHom hp m' ≫ m.1.1)
  rw [Category.assoc, hfac, ← Category.assoc, key, Category.assoc]

/-- **The shear map.** The morphism of presheaves `Isom^α(x₁, x₂) ×_𝒯 Isom^α(x₁, x₂) ⟶
Isom^{id}(x₂, x₂)` sending a pair `(m, m')` to `m'⁻¹ ≫ m`. -/
noncomputable def shearMap (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    Presheaf.fibreProduct (terminal.from (relVertHomPresheaf hq hp hY hF))
        (terminal.from (relVertHomPresheaf hq hp hY hF)) ⟶
      relVertHomPresheaf hq hp (diagPoint_comp_relProdP hY hF) hF where
  app _ := ↾fun x => shear hp hF x.1.1 x.1.2
  naturality _ _ h := by
    ext x
    exact shear_restrict hq hp hY hF h.unop x.1.1 x.1.2

/-- **The self-fibre-product of the fibre of the relative diagonal is a base change of the
automorphism presheaf.** The shear map and the second projection of
`Isom^α(x₁, x₂) ×_𝒯 Isom^α(x₁, x₂)` form a cartesian square over the structural morphisms of
`Isom^{id}(x₂, x₂)` and `Isom^α(x₁, x₂)`: over a fixed second component the shear is a bijection
onto the sections of `Isom^{id}(x₂, x₂)`, with inverse the unshear. -/
theorem isPullback_shearMap (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    IsPullback (shearMap hq hp hY hF)
      (Presheaf.fibreProductSnd (terminal.from (relVertHomPresheaf hq hp hY hF))
        (terminal.from (relVertHomPresheaf hq hp hY hF)))
      (terminal.from (relVertHomPresheaf hq hp (diagPoint_comp_relProdP hY hF) hF))
      (terminal.from (relVertHomPresheaf hq hp hY hF)) := by
  rw [IsPullback.iff_app]
  intro V
  have hterm : IsTerminal ((⊤_ (𝒯ᵒᵖ ⥤ Type v₃)).obj V) :=
    terminalIsTerminal.isTerminalObj ((evaluation 𝒯ᵒᵖ (Type v₃)).obj V)
  have _ : Unique ((⊤_ (𝒯ᵒᵖ ⥤ Type v₃)).obj V) := Types.isTerminalEquivUnique _ hterm
  rw [Types.isPullback_iff]
  refine ⟨hterm.hom_ext _ _, ?_, ?_⟩
  · rintro x y ⟨h₁, h₂⟩
    have h₁' : shear hp hF x.1.1 x.1.2 = shear hp hF y.1.1 y.1.2 := h₁
    have h₂' : x.1.2 = y.1.2 := h₂
    refine Subtype.ext (Prod.ext ?_ h₂')
    have e1 := unshear_shear hp hF x.1.1 x.1.2
    have e2 := unshear_shear hp hF y.1.1 y.1.2
    rw [← e1, ← e2, h₁', h₂']
  · intro b m _
    refine ⟨⟨(unshear hF b m, m), Subsingleton.elim _ _⟩, ?_, rfl⟩
    exact shear_unshear hp hF b m

/-- **The second projection of `Isom^α ×_𝒯 Isom^α` is the base change of `Isom^{id} ⟶ 𝒯`.** The
two arrows over `Isom^α(x₁, x₂)` are compared by the shear map: both squares of
`CategoryTheory.Presheaf.isPullback_fibreProduct` and
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.isPullback_shearMap` have the same
apex and the same second projection, so the two fibre products they identify are isomorphic over
it. -/
noncomputable def arrowIsoPullbackSndShear (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    Arrow.mk (pullback.snd (terminal.from (relVertHomPresheaf hq hp hY hF))
        (terminal.from (relVertHomPresheaf hq hp hY hF))) ≅
      Arrow.mk (pullback.snd
        (terminal.from (relVertHomPresheaf hq hp (diagPoint_comp_relProdP hY hF) hF))
        (terminal.from (relVertHomPresheaf hq hp hY hF))) :=
  Arrow.isoMk
    ((Presheaf.isPullback_fibreProduct (terminal.from (relVertHomPresheaf hq hp hY hF))
        (terminal.from (relVertHomPresheaf hq hp hY hF))).isoPullback.symm ≪≫
      (isPullback_shearMap hq hp hY hF).isoPullback)
    (Iso.refl _)
    (by
      simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
        Category.assoc]
      rw [IsPullback.isoPullback_hom_snd (isPullback_shearMap hq hp hY hF),
        IsPullback.isoPullback_inv_snd])

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
