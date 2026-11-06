module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
import all
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# Algebraic spaces over a test scheme, as presheaves on the slice

Let `S` be a scheme of a big fppf site and `U` a scheme over `S` of the site.  By Stacks 00Y1 a
presheaf `G` on the slice `(Sch/S)_{fppf}/U` is the same thing as a presheaf on `(Sch/S)_{fppf}`
together with a morphism to `h_U`, namely the coproduct presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` (`CategoryTheory.OverShriek.presheaf`).  Call `G` *algebraic* when
that presheaf is an algebraic space over `S`.

This file records what condition (2) of Stacks 045G needs from that notion:

* algebraic presheaves on the slice are closed under isomorphism, under fibre products, and
  contain the terminal presheaf, because the equivalence of Stacks 00Y1 preserves limits and the
  forgetful functor from presheaves over `h_U` preserves fibre products;
* an algebraic presheaf on the slice over `U` is an algebraic space over `U`, after transport to
  the big fppf site of `U` along the iterated slice equivalence; so an isomorphism sheaf
  `Isom(x, y)` that is a universe lift of an algebraic presheaf on the slice is an algebraic space
  over `U`;
* if all the sections of `Isom(x, y)` live over a monomorphism `j : Z ⟶ U`, then `Isom(x, y)` is
  algebraic as soon as the isomorphism sheaf of the restrictions of `x` and `y` to `Z` is.  This is
  the step "we may replace `T` by `Z`" of the proofs of Stacks 08W6 and Stacks 0DLG.

## Main definitions

* `AlgebraicGeometry.Stack.IsAlgebraicOverSlice`: a presheaf on the slice over `U` is algebraic.
* `AlgebraicGeometry.Stack.extendAlong`: the extension of a presheaf on the slice over `Z` to the
  slice over `U` along `j : Z ⟶ U`, whose sections over `g : V ⟶ U` are the pairs of a
  factorization `g = k ≫ j` and a section over `k`.

## Main results

* `AlgebraicGeometry.Stack.IsAlgebraicOverSlice.of_iso`, `.pullback`, `.of_isTerminal`: the closure
  properties.
* `AlgebraicGeometry.Stack.isomPresheaf_algebraic_of_isAlgebraicOverSlice`: an isomorphism sheaf
  which is a lift of an algebraic presheaf on the slice is an algebraic space over the base scheme.
* `AlgebraicGeometry.Stack.exists_isAlgebraicOverSlice_isomPresheaf_of_mono`: under a
  monomorphism containing the support of `Isom(x, y)`, the isomorphism sheaf is the extension of
  the isomorphism sheaf of the restrictions, so it lifts an algebraic presheaf on the slice as soon
  as the latter does.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Extension along a morphism of the base -/

section Extend

variable {C : Type*} [Category.{v} C] {Z U : C} (j : Z ⟶ U)

/-- Two restrictions of a section along morphisms of the slice with the same underlying morphism
give the same pair of a morphism to the base and a section. -/
theorem sigma_restrict_eq (H : (Over Z)ᵒᵖ ⥤ Type w) {V W : C} {φ : W ⟶ Z}
    (s : H.obj (op (Over.mk φ))) {ψ ψ' : V ⟶ Z} (e : Over.mk ψ ⟶ Over.mk φ)
    (e' : Over.mk ψ' ⟶ Over.mk φ) (h : e.left = e'.left) :
    (⟨ψ, H.map e.op s⟩ : Σ χ : V ⟶ Z, H.obj (op (Over.mk χ))) = ⟨ψ', H.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  obtain rfl : ψ = ψ' := by rw [← h1, ← h2, h]
  rw [Over.OverMorphism.ext h]

/-- **The extension of a presheaf on the slice over `Z` along `j : Z ⟶ U`.**  Its sections over
`g : V ⟶ U` are the pairs of a morphism `k : V ⟶ Z` with `k ≫ j = g` and a section of `H` over
`k`; the restriction along `h : g₁ ⟶ g₂` composes `k` with `h` and restricts the section. -/
def extendAlong (H : (Over Z)ᵒᵖ ⥤ Type (max v w)) : (Over U)ᵒᵖ ⥤ Type (max v w) where
  obj g := {p : Σ k : g.unop.left ⟶ Z, H.obj (op (Over.mk k)) // p.1 ≫ j = g.unop.hom}
  map {g₁ g₂} h := ↾fun p => ⟨⟨h.unop.left ≫ p.1.1,
      H.map (Over.homMk h.unop.left rfl : Over.mk (h.unop.left ≫ p.1.1) ⟶ Over.mk p.1.1).op p.1.2⟩,
    by rw [Category.assoc, p.2, Over.w h.unop]⟩
  map_id g := by
    ext ⟨⟨k, t⟩, hk⟩ : 3
    refine Subtype.ext ?_
    have h := sigma_restrict_eq H t (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 _ ≫ k) ⟶ Over.mk k)
      (𝟙 (Over.mk k)) rfl
    rwa [op_id, H.map_id, types_id_apply] at h
  map_comp f g := by
    ext ⟨⟨k, t⟩, hk⟩ : 3
    refine Subtype.ext ?_
    have h := sigma_restrict_eq H t
      (Over.homMk (f ≫ g).unop.left rfl :
        Over.mk ((f ≫ g).unop.left ≫ k) ⟶ Over.mk k)
      ((Over.homMk g.unop.left rfl : Over.mk (g.unop.left ≫ f.unop.left ≫ k) ⟶
          Over.mk (f.unop.left ≫ k)) ≫
        (Over.homMk f.unop.left rfl : Over.mk (f.unop.left ≫ k) ⟶ Over.mk k)) (by simp)
    rwa [op_comp, Functor.map_comp_apply] at h

/-- The sections of `AlgebraicGeometry.Stack.extendAlong` over `g` are the pairs of a
factorization `k` of `g` through `j` and a section of `H` over `k`. -/
@[simp]
theorem extendAlong_obj (H : (Over Z)ᵒᵖ ⥤ Type (max v w)) (g : (Over U)ᵒᵖ) :
    (extendAlong j H).obj g =
      {p : Σ k : g.unop.left ⟶ Z, H.obj (op (Over.mk k)) // p.1 ≫ j = g.unop.hom} :=
  rfl

/-- The restriction maps of `AlgebraicGeometry.Stack.extendAlong`, on the underlying pairs. -/
theorem extendAlong_map_coe (H : (Over Z)ᵒᵖ ⥤ Type (max v w)) {g₁ g₂ : (Over U)ᵒᵖ} (h : g₁ ⟶ g₂)
    (p : (extendAlong j H).obj g₁) :
    ((extendAlong j H).map h p).1 = ⟨h.unop.left ≫ p.1.1,
      H.map (Over.homMk h.unop.left rfl : Over.mk (h.unop.left ≫ p.1.1) ⟶ Over.mk p.1.1).op
        p.1.2⟩ :=
  rfl

/-- The extension along `j` of a morphism of presheaves on the slice over `Z`. -/
def extendAlongMap {H H' : (Over Z)ᵒᵖ ⥤ Type (max v w)} (α : H ⟶ H') :
    extendAlong j H ⟶ extendAlong j H' where
  app g := ↾fun p => ⟨⟨p.1.1, α.app _ p.1.2⟩, p.2⟩
  naturality {g₁ g₂} h := by
    ext p : 3
    exact Subtype.ext <| congrArg (Sigma.mk (h.unop.left ≫ p.1.1))
      (NatTrans.naturality_apply α _ p.1.2)

/-- `AlgebraicGeometry.Stack.extendAlongMap` applies `α` to the section and keeps the
factorization. -/
theorem extendAlongMap_app_coe {H H' : (Over Z)ᵒᵖ ⥤ Type (max v w)} (α : H ⟶ H')
    (g : (Over U)ᵒᵖ) (p : (extendAlong j H).obj g) :
    ((extendAlongMap j α).app g p).1 = ⟨p.1.1, α.app _ p.1.2⟩ :=
  rfl

/-- The extension along `j` of an isomorphism of presheaves on the slice over `Z`. -/
def extendAlongIso {H H' : (Over Z)ᵒᵖ ⥤ Type (max v w)} (α : H ≅ H') :
    extendAlong j H ≅ extendAlong j H' :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun p => ⟨⟨p.1.1, α.hom.app _ p.1.2⟩, p.2⟩
      invFun := fun p => ⟨⟨p.1.1, α.inv.app _ p.1.2⟩, p.2⟩
      left_inv := fun p => Subtype.ext (Sigma.ext rfl
        (heq_of_eq (α.hom_inv_id_app_apply (op (Over.mk p.1.1)) p.1.2)))
      right_inv := fun p => Subtype.ext (Sigma.ext rfl
        (heq_of_eq (α.inv_hom_id_app_apply (op (Over.mk p.1.1)) p.1.2))) })
    (fun h => (extendAlongMap j α.hom).naturality h)

/-- Extension along `j` commutes with universe lifts. -/
def extendAlongULift (H : (Over Z)ᵒᵖ ⥤ Type (max v w)) :
    extendAlong.{v, max w w'} j (H ⋙ uliftFunctor.{w'}) ≅ extendAlong j H ⋙ uliftFunctor.{w'} :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun p => ⟨⟨⟨p.1.1, p.1.2.down⟩, p.2⟩⟩
      invFun := fun p => ⟨⟨p.down.1.1, ⟨p.down.1.2⟩⟩, p.down.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- The morphism of the slice over `U` from `g` to `k ≫ j`, for a factorization `g = k ≫ j`. -/
def factorHom {g : Over U} {k : g.left ⟶ Z} (hk : k ≫ j = g.hom) : g ⟶ Over.mk (k ≫ j) :=
  Over.homMk (𝟙 g.left) (by simp [hk])

/-- `AlgebraicGeometry.Stack.factorHom` is an isomorphism: its underlying morphism is the
identity. -/
instance {g : Over U} {k : g.left ⟶ Z} (hk : k ≫ j = g.hom) : IsIso (factorHom j hk) :=
  ⟨⟨Over.homMk (𝟙 _) (by simp [hk]), Over.OverMorphism.ext (by simp [factorHom]),
    Over.OverMorphism.ext (by simp [factorHom])⟩⟩

/-- **A presheaf on the slice over `U` supported over a monomorphism `j : Z ⟶ U` is the extension
of its restriction.**  If every section of `F` lies over an object of the slice whose morphism to
`U` factors through `j`, the restriction maps along the identifications `V →g U = V →k Z →j U`
assemble to an isomorphism `extendAlong j ((Over.map j)^* F) ≅ F`. -/
def extendAlongRestrictIso [Mono j] (F : (Over U)ᵒᵖ ⥤ Type (max v w))
    (hF : ∀ g : Over U, Nonempty (F.obj (op g)) → ∃ k : g.left ⟶ Z, k ≫ j = g.hom) :
    extendAlong j ((Over.map j).op ⋙ F) ≅ F := by
  let φ : ∀ g : (Over U)ᵒᵖ, (extendAlong j ((Over.map j).op ⋙ F)).obj g → F.obj g :=
    fun g p => F.map (factorHom j p.2).op p.1.2
  have hinj : ∀ g, Function.Injective (φ g) := by
    rintro g ⟨⟨k, t⟩, hk⟩ ⟨⟨k', t'⟩, hk'⟩ h
    obtain rfl : k = k' := (cancel_mono j).1 (hk.trans hk'.symm)
    exact Subtype.ext (Sigma.ext rfl
      (heq_of_eq (((isIso_iff_bijective (F.map (factorHom j hk).op)).1 inferInstance).1 h)))
  have hsurj : ∀ g, Function.Surjective (φ g) := by
    intro g s
    obtain ⟨k, hk⟩ := hF g.unop ⟨s⟩
    obtain ⟨t, ht⟩ := ((isIso_iff_bijective (F.map (factorHom j hk).op)).1 inferInstance).2 s
    exact ⟨⟨⟨k, t⟩, hk⟩, ht⟩
  refine NatIso.ofComponents
    (fun g => (Equiv.ofBijective (φ g) ⟨hinj g, hsurj g⟩).toIso) ?_
  rintro g₁ g₂ h
  ext ⟨⟨k, t⟩, hk⟩ : 3
  change F.map (factorHom j (k := h.unop.left ≫ k) (by rw [Category.assoc, hk, Over.w h.unop])).op
      (F.map ((Over.map j).map
        (Over.homMk h.unop.left rfl : Over.mk (h.unop.left ≫ k) ⟶ Over.mk k)).op t) =
    F.map h (F.map (factorHom j hk).op t)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  refine congrArg (fun m => F.map m t) ?_
  apply Quiver.Hom.unop_inj
  ext
  simp [factorHom]

/-- The coproduct presheaf of an extension along `j` is the coproduct presheaf of the presheaf
extended: a pair of `g : V ⟶ U` and a factorization `g = k ≫ j` with a section over `k` is the
same thing as `k` with a section over it. -/
def presheafExtendAlongIso (G : (Over Z)ᵒᵖ ⥤ Type v) :
    OverShriek.presheaf (extendAlong.{v, v} j G) ≅ OverShriek.presheaf G :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun p => p.2.1
      invFun := fun p => ⟨p.1 ≫ j, ⟨p, rfl⟩⟩
      left_inv := by
        rintro ⟨φ, ⟨p, hp⟩⟩
        have key : ∀ (φ' : V.unop ⟶ U) (h : p.1 ≫ j = φ'),
            (⟨p.1 ≫ j, ⟨p, rfl⟩⟩ : Σ φ : V.unop ⟶ U, (extendAlong.{v, v} j G).obj
              (op (Over.mk φ))) = ⟨φ', ⟨p, h⟩⟩ := by
          rintro _ rfl
          rfl
        exact key φ hp
      right_inv := fun _ => rfl })
    (fun _ => rfl)

end Extend

/-- Pullbacks of presheaves of sets (instance search times out without this shortcut). -/
local instance (priority := high) hasLimit_cospan_presheaf_IsomPresheafSliceAlgebraic
    {C : Type*} [Category C] {X Y Z : Cᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Algebraic presheaves on the slice -/

/-- A presheaf `G` on the slice of the big fppf site of `S` over `U` is *algebraic* when the
presheaf over `h_U` it corresponds to by Stacks 00Y1, the coproduct presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V →φ U)`, is an algebraic space over `S`. -/
def IsAlgebraicOverSlice {U : BigFppfOver B S hS} (G : (Over U)ᵒᵖ ⥤ Type u) : Prop :=
  IsAlgebraicSpace B S hS (OverShriek.presheaf G)

namespace IsAlgebraicOverSlice

variable {U : BigFppfOver B S hS}

/-- Being algebraic is invariant under isomorphism of presheaves on the slice. -/
theorem of_iso {G G' : (Over U)ᵒᵖ ⥤ Type u} (e : G ≅ G') (h : IsAlgebraicOverSlice G) :
    IsAlgebraicOverSlice G' :=
  Space.isAlgebraicSpace_of_iso B S hS
    (show OverShriek.presheaf G ≅ OverShriek.presheaf G' from OverShriek.presheafFunctor.mapIso e) h

/-- The presheaf on the slice of an object over `h_U` is algebraic as soon as that object is an
algebraic space: the counit of Stacks 00Y1 identifies the two. -/
theorem of_over (T : Over (yoneda.obj U)) (hT : IsAlgebraicSpace B S hS T.left) :
    IsAlgebraicOverSlice ((OverShriek.presheafEquivalence (U := U)).inverse.obj T) :=
  Space.isAlgebraicSpace_of_iso B S hS
    (show T.left ≅ OverShriek.presheaf ((OverShriek.presheafEquivalence (U := U)).inverse.obj T)
      from (Over.forget _).mapIso ((OverShriek.presheafEquivalence (U := U)).counitIso.app T).symm)
    hT

/-- A terminal presheaf on the slice is algebraic: it corresponds to `h_U` itself. -/
theorem of_isTerminal {G : (Over U)ᵒᵖ ⥤ Type u} (hG : IsTerminal G) : IsAlgebraicOverSlice G :=
  Space.isAlgebraicSpace_of_iso B S hS
    (show yoneda.obj U ≅ OverShriek.presheaf G from (Over.forget _).mapIso
      ((hG.isTerminalObj (OverShriek.presheafEquivalence (U := U)).functor G).uniqueUpToIso
        Over.mkIdTerminal).symm)
    (isAlgebraicSpace_yoneda B S hS U)

/-- **Algebraic presheaves on the slice are closed under fibre products.**  The equivalence of
Stacks 00Y1 preserves fibre products, and so does the forgetful functor from presheaves over
`h_U` to presheaves, so the fibre product is a fibre product of algebraic spaces over `S`. -/
theorem pullback {G₁ G₂ G₃ : (Over U)ᵒᵖ ⥤ Type u} (f : G₁ ⟶ G₃) (g : G₂ ⟶ G₃)
    (h₁ : IsAlgebraicOverSlice G₁) (h₂ : IsAlgebraicOverSlice G₂)
    (h₃ : IsAlgebraicOverSlice G₃) : IsAlgebraicOverSlice (Limits.pullback f g) := by
  let Φ := (OverShriek.presheafEquivalence (U := U)).functor ⋙ Over.forget (yoneda.obj U)
  exact Space.isAlgebraicSpace_of_iso B S hS
    (show Limits.pullback (Φ.map f) (Φ.map g) ≅ OverShriek.presheaf (Limits.pullback f g) from
      (PreservesPullback.iso Φ f g).symm)
    (isAlgebraicSpace_pullback B S hS (Φ.map f) (Φ.map g) h₁ h₂ h₃)

/-- The extension of an algebraic presheaf along a morphism of the base is algebraic: both have
the same coproduct presheaf. -/
theorem extendAlong {Z : BigFppfOver B S hS} (j : Z ⟶ U) {G : (Over Z)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicOverSlice G) : IsAlgebraicOverSlice (extendAlong.{u, u} j G) :=
  Space.isAlgebraicSpace_of_iso B S hS (presheafExtendAlongIso j G).symm h

end IsAlgebraicOverSlice

/-! ### Universe lifts of algebraic presheaves on the slice -/

/-- A presheaf of possibly large sets on the slice over `U` is *a lift of an algebraic one* when it
is isomorphic to the universe lift of an algebraic presheaf on the slice. -/
def IsULiftAlgebraicOverSlice {U : BigFppfOver B S hS} (F : (Over U)ᵒᵖ ⥤ Type (max u w)) : Prop :=
  ∃ G : (Over U)ᵒᵖ ⥤ Type u, IsAlgebraicOverSlice G ∧ Nonempty (G ⋙ uliftFunctor.{w} ≅ F)

namespace IsULiftAlgebraicOverSlice

variable {U : BigFppfOver B S hS}

/-- Lifts of algebraic presheaves are closed under isomorphism. -/
theorem of_iso {F F' : (Over U)ᵒᵖ ⥤ Type (max u w)} (e : F ≅ F')
    (h : IsULiftAlgebraicOverSlice F) : IsULiftAlgebraicOverSlice F' :=
  h.imp fun _ ⟨hG, ⟨e'⟩⟩ => ⟨hG, ⟨e' ≪≫ e⟩⟩

/-- A terminal presheaf is a lift of an algebraic one. -/
theorem of_isTerminal {F : (Over U)ᵒᵖ ⥤ Type (max u w)} (hF : IsTerminal F) :
    IsULiftAlgebraicOverSlice F := by
  let W := (Functor.whiskeringRight (Over U)ᵒᵖ (Type u) (Type (max u w))).obj uliftFunctor.{w}
  exact ⟨⊤_ _, IsAlgebraicOverSlice.of_isTerminal terminalIsTerminal,
    ⟨(terminalIsTerminal.isTerminalObj W _).uniqueUpToIso hF⟩⟩

/-- **Lifts of algebraic presheaves are closed under fibre products.** -/
theorem of_isPullback {F₁ F₂ F₃ F₄ : (Over U)ᵒᵖ ⥤ Type (max u w)} {t : F₁ ⟶ F₂} {l : F₁ ⟶ F₃}
    {r : F₂ ⟶ F₄} {b : F₃ ⟶ F₄} (h : IsPullback t l r b) (h₂ : IsULiftAlgebraicOverSlice F₂)
    (h₃ : IsULiftAlgebraicOverSlice F₃) (h₄ : IsULiftAlgebraicOverSlice F₄) :
    IsULiftAlgebraicOverSlice F₁ := by
  obtain ⟨G₂, hG₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨G₃, hG₃, ⟨e₃⟩⟩ := h₃
  obtain ⟨G₄, hG₄, ⟨e₄⟩⟩ := h₄
  let W := (Functor.whiskeringRight (Over U)ᵒᵖ (Type u) (Type (max u w))).obj uliftFunctor.{w}
  let hW : W.FullyFaithful := fullyFaithfulULiftFunctor.whiskeringRight _
  let r' : G₂ ⟶ G₄ := hW.preimage (e₂.hom ≫ r ≫ e₄.inv)
  let b' : G₃ ⟶ G₄ := hW.preimage (e₃.hom ≫ b ≫ e₄.inv)
  have h' : IsPullback (W.map (pullback.fst r' b') ≫ e₂.hom) (W.map (pullback.snd r' b') ≫ e₃.hom)
      r b :=
    ((IsPullback.of_hasPullback r' b').map W).of_iso (Iso.refl _) e₂ e₃ e₄ (by simp) (by simp)
      (by simp [r', Functor.FullyFaithful.map_preimage])
      (by simp [b', Functor.FullyFaithful.map_preimage])
  exact ⟨pullback r' b', IsAlgebraicOverSlice.pullback r' b' hG₂ hG₃ hG₄,
    ⟨h'.isoIsPullback _ _ h⟩⟩

end IsULiftAlgebraicOverSlice

/-! ### From the slice to the big fppf site of the base scheme -/

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **An isomorphism sheaf which lifts an algebraic presheaf on the slice is an algebraic space
over the base scheme.**  If `G` is an algebraic presheaf on the slice over `U` whose universe lift
is isomorphic to that of `Isom(x, y)`, then `Isom(x, y)`, read on the big fppf site of `U`, is an
algebraic space over `U` in the sense of condition (2) of Stacks 045G.

The algebraic space is the fibre over the tautological section of the coproduct presheaf of `G`,
which is `G` itself by Stacks 00Y1, transported along the iterated slice equivalence; it is an
algebraic space over `U` by Stacks 03I5. -/
theorem isomPresheaf_algebraic_of_isAlgebraicOverSlice {U : BigFppfOver B S hS}
    (x y : (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered; 𝒳.val.p.Fiber U))
    (G : (Over U)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicOverSlice G)
    (e : G ⋙ uliftFunctor.{v, u} ≅
      (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
       𝒳.val.p.isomPresheaf x y) ⋙ uliftFunctor.{u, v}) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 F ∧
        Nonempty (F ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x y) ⋙
            uliftFunctor.{u, v}) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let q := OverShriek.presheafToYoneda G
  exact ⟨(Over.iteratedSliceBackward U).op ⋙ OverShriek.fiber (𝟙 _) q,
    isAlgebraicSpace_iteratedSliceFiber B S hS U q hG, ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
        (Functor.isoWhiskerRight (OverShriek.presheafUnitIsoApp G).symm uliftFunctor.{v, u} ≪≫ e)
      ≪≫ (Functor.associator _ _ _).symm⟩⟩

/-- **Restriction to a monomorphism containing the support of `Isom(x, y)`.**  Let `j : Z ⟶ U`
be a monomorphism and `x'`, `y'` objects over `Z` isomorphic to the pullbacks of `x`, `y` along
`j`.  If every section of `Isom(x, y)` lives over a morphism `V ⟶ U` factoring through `j`, and
`Isom(x', y')` is a universe lift of an algebraic presheaf `G` on the slice over `Z`, then
`Isom(x, y)` is a universe lift of an algebraic presheaf on the slice over `U`, namely the
extension of `G` along `j`. -/
theorem exists_isAlgebraicOverSlice_isomPresheaf_of_mono {Z U : BigFppfOver B S hS} (j : Z ⟶ U)
    [Mono j]
    (x y : (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered; 𝒳.val.p.Fiber U))
    (x' y' : (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered; 𝒳.val.p.Fiber Z))
    (ex : (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      x' ≅ 𝒳.val.p.pullbackFiber x j))
    (ey : (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      y' ≅ 𝒳.val.p.pullbackFiber y j))
    (hsupp : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ g : Over U, Nonempty ((𝒳.val.p.isomPresheaf x y).obj (op g)) →
        ∃ k : g.left ⟶ Z, k ≫ j = g.hom)
    (G : (Over Z)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicOverSlice G)
    (e : G ⋙ uliftFunctor.{v, u} ≅
      (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
       𝒳.val.p.isomPresheaf x' y') ⋙ uliftFunctor.{u, v}) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∃ G' : (Over U)ᵒᵖ ⥤ Type u, IsAlgebraicOverSlice G' ∧
      Nonempty (G' ⋙ uliftFunctor.{v, u} ≅ 𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v}) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  refine ⟨extendAlong.{u, u} j G, hG.extendAlong j, ⟨?_⟩⟩
  have c : 𝒳.val.p.isomPresheaf x' y' ⋙ uliftFunctor.{u, v} ≅
      (Over.map j).op ⋙ 𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v} :=
    Functor.isoWhiskerRight (isomPresheafIsoOfIso 𝒳.val.p ex ey ≪≫
      isomPresheafPullbackCompIso 𝒳.val.p x y j) uliftFunctor.{u, v} ≪≫ Functor.associator _ _ _
  have hsupp' : ∀ g : Over U,
      Nonempty ((𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v}).obj (op g)) →
        ∃ k : g.left ⟶ Z, k ≫ j = g.hom :=
    fun g ⟨s⟩ => hsupp g ⟨s.down⟩
  exact (extendAlongULift.{u, u, v} j G).symm ≪≫ extendAlongIso j (e ≪≫ c) ≪≫
    extendAlongRestrictIso j _ hsupp'

end AlgebraicGeometry.Stack

end
