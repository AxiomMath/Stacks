module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# The set-theoretic condition for a directed colimit (Stacks 0AIS)

Let `X` be the colimit, among the fppf sheaves over a scheme `S` in a big fppf site `B`, of a
nonempty directed diagram `D` of affine schemes over `S` whose transition morphisms are
thickenings. **Stacks 0AIS** asks, of an affine formal algebraic space, that it receive a
surjection from a representable sheaf whose kernel pair in turn receives a surjection from a
representable sheaf — the predicate
`AlgebraicGeometry.FormalSpace.SatisfiesSetTheoreticCondition`. Here that condition is deduced
for `X` from the one hypothesis that the *coproduct* of the represented stages of `D` is
representable by an object `U` of the site.

The surjection is then the canonical map `U ⟶ X` out of that coproduct: a colimit over a
directed index is the quotient of the coproduct of its stages, so the composite
`U ≅ ∐ᵢ Dᵢ ⟶ colim Dᵢ ≅ X` is an epimorphism. For its kernel pair, the object
`A = U ×_{⊤} U` of the site represents `U ⨯ U`, and `U ×_X U` is the base change of the diagonal
of `X` along `A ⟶ X ⨯ X`; that base change is representable by an object of the site precisely
because the diagonal of `X` is representable, which is **Stacks 0AI8**
(`AlgebraicGeometry.FormalSpace.diagonal_isClosedImmersion`). So the kernel pair is itself
represented, and the second surjection may be taken to be an isomorphism.

Only the *surjection* needs the coproduct; the kernel pair is handled by the diagonal, which the
colimit presentation supplies on its own. So the argument splits, and
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`
asks for nothing but a surjection onto `X` from the sheaf of an object of the site, however
obtained — from the coproduct of the stages, or by base change of a surjection onto another
sheaf along a representable morphism, which is how a colimit lying over a space that already
satisfies the condition inherits it.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`:
  the set-theoretic condition for such a colimit, from a surjection onto it from the sheaf of an
  object of the site.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`:
  the set-theoretic condition for such a colimit, when the coproduct of its stages is
  representable.

## Implementation notes

The colimit and the coproduct are formed among fppf sheaves of `Type (u + 1)`, not among
presheaves. Representability is recorded, as in `AlgebraicGeometry.FormalSpace.Affine`, by an
isomorphism of underlying presheaves with a universe-lifted Yoneda presheaf, so nothing here
presupposes that the chosen big fppf site is subcanonical; subcanonicity is a *theorem* about it
(`AlgebraicGeometry.BigFppfSite.subcanonical_topology`) and is what identifies
`CategoryTheory.Sheaf.sheafifiedYoneda` with `CategoryTheory.GrothendieckTopology.uliftYoneda`,
hence makes the sheafified Yoneda embedding preserve the finite limits used above.

The purely categorical step — `U ×_X U` from the base change of the diagonal along `A ⟶ X ⨯ X` —
is isolated as the private `nonempty_iso_pullback_of_isPullback_diag`, stated for an arbitrary
category with a terminal object, binary products and pullbacks, since it uses no property of
sheaves.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

universe w₁ w₂

/-- The category of `Type (u + 1)`-valued sheaves for a Grothendieck topology on the big fppf
site over `S` has all colimits of size `u + 1`. -/
noncomputable local instance sheaf_hasColimits
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (J : GrothendieckTopology (BigFppfOver B S hS)) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) :=
  Sheaf.instHasColimitsOfSize

/-- In a category with a terminal object, binary products and pullbacks, let `fU : Y ⟶ X` be a
morphism, let `q₁, q₂ : A ⟶ Y` exhibit `A` as the kernel pair of `fU` *over the terminal object*
— i.e. as `Y ×_{⊤} Y` — and let `R` be the base change of the diagonal of `X` along
`⟨q₁ ≫ fU, q₂ ≫ fU⟩ : A ⟶ X ⨯ X`. Then `R` is the kernel pair `Y ×_X Y` of `fU`. -/
private theorem nonempty_iso_pullback_of_isPullback_diag
    {C : Type w₁} [Category.{w₂} C] [HasTerminal C] [HasBinaryProducts C] [HasPullbacks C]
    {X Y A R : C} (fU : Y ⟶ X) {q₁ q₂ : A ⟶ Y}
    (hA : IsPullback q₁ q₂ (fU ≫ terminal.from X) (fU ≫ terminal.from X))
    {fstR : R ⟶ X} {sR : R ⟶ A}
    (hpb : IsPullback fstR sR (diag X) (prod.lift (q₁ ≫ fU) (q₂ ≫ fU))) :
    Nonempty (R ≅ pullback fU fU) := by
  let i : X ⟶ ⊤_ C := terminal.from X
  let eA := hA.isoPullback
  have heAfst : eA.hom ≫ pullback.fst (fU ≫ i) (fU ≫ i) = q₁ := hA.isoPullback_hom_fst
  have heAsnd : eA.hom ≫ pullback.snd (fU ≫ i) (fU ≫ i) = q₂ := hA.isoPullback_hom_snd
  have hXprod : IsPullback (prod.fst : X ⨯ X ⟶ X) prod.snd i i :=
    IsPullback.of_isLimit_cone
      (isPullbackOfIsTerminalIsProduct i i prod.fst prod.snd terminalIsTerminal (prodIsProd X X))
  have hXpb : IsPullback (pullback.fst i i) (pullback.snd i i) i i :=
    IsPullback.of_hasPullback i i
  let eXprod := hXprod.isoIsPullback X X hXpb
  have hCan := pullback_map_diagonal_isPullback fU fU i
  obtain ⟨gCan, hgCanFst, hgCanSnd, hCanEq⟩ :
      ∃ g : pullback (fU ≫ i) (fU ≫ i) ⟶ pullback i i,
        g ≫ pullback.fst i i = pullback.fst (fU ≫ i) (fU ≫ i) ≫ fU ∧
          g ≫ pullback.snd i i = pullback.snd (fU ≫ i) (fU ≫ i) ≫ fU ∧
          g = pullback.map (fU ≫ i) (fU ≫ i) i i fU fU (𝟙 _) (by simp) (by simp) :=
    ⟨pullback.map (fU ≫ i) (fU ≫ i) i i fU fU (𝟙 _) (by simp) (by simp),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩
  rw [← hCanEq] at hCan
  have hRel : IsPullback fstR (sR ≫ eA.hom) (pullback.diagonal i) gCan := by
    apply hpb.of_iso (Iso.refl _) (Iso.refl _) eA eXprod
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.id_comp]
      apply pullback.hom_ext
      · simp [eXprod, IsPullback.isoIsPullback_hom_fst X X hXprod hXpb]
      · simp [eXprod, IsPullback.isoIsPullback_hom_snd X X hXprod hXpb]
    · apply pullback.hom_ext
      · simp [eXprod, IsPullback.isoIsPullback_hom_fst X X hXprod hXpb, ← heAfst, hgCanFst]
      · simp [eXprod, IsPullback.isoIsPullback_hom_snd X X hXprod hXpb, ← heAsnd, hgCanSnd]
  exact ⟨hRel.isoIsPullback X (pullback (fU ≫ i) (fU ≫ i)) hCan⟩

/-- On a subcanonical site, the `Type (u + 1)`-valued sheafified Yoneda embedding is isomorphic to
the universe-lifted Yoneda embedding. -/
private noncomputable def uliftYonedaIsoSheafifiedYoneda {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [J.Subcanonical] :
    J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
  (Functor.isoWhiskerLeft J.uliftYoneda
    (sheafificationNatIso.{u, u + 1, u + 1, u + 2} J (Type (u + 1)))) ≪≫
    Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf (presheafToSheaf J (Type (u + 1)))

/-- The topology of the big fppf site over `S` is subcanonical. -/
private theorem subcanonical_bigFppfOver_topology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (BigFppfOver.topology B S hS).Subcanonical :=
  have := BigFppfSite.subcanonical_topology B
  inferInstanceAs (B.topology.over (B.obj hS)).Subcanonical

/-- **The set-theoretic condition for a directed colimit, from a representable surjection.** A
directed colimit `X` of affine fppf sheaves along thickenings satisfies the set-theoretic
condition `AlgebraicGeometry.FormalSpace.SatisfiesSetTheoreticCondition` as soon as the sheaf of
*one* object `U` of the site surjects onto it. -/
public theorem satisfiesSetTheoreticCondition_of_colimit_of_representable_epi
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : Nonempty (X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))))
    (U : BigFppfOver B S hS)
    (fU : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (hfU : Epi fU) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := subcanonical_bigFppfOver_topology B S hS
  let K := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  let eX : colimit K ≅ X := (Classical.choice hX).symm
  let eH := uliftYonedaIsoSheafifiedYoneda J
  let : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_of_natIso eH
  let A := pullback (terminal.from U) (terminal.from U)
  let p₁ : A ⟶ U := pullback.fst _ _
  let p₂ : A ⟶ U := pullback.snd _ _
  let gA : (Sheaf.sheafifiedYoneda J).obj A ⟶ X ⨯ X :=
    prod.lift ((Sheaf.sheafifiedYoneda J).map p₁ ≫ fU) ((Sheaf.sheafifiedYoneda J).map p₂ ≫ fU)
  let hRep := (diagonal_isClosedImmersion B S hS D hD X eX).1
  let R := hRep.pullback gA
  have hpb := hRep.isPullback gA
  let T := (Sheaf.sheafifiedYoneda J).obj (⊤_ (BigFppfOver B S hS))
  let : PreservesLimit (Functor.empty (BigFppfOver B S hS)) (Sheaf.sheafifiedYoneda J) :=
    preservesLimit_of_natIso (Functor.empty _) eH
  have hT : IsTerminal T :=
    (terminalIsTerminal : IsTerminal (⊤_ (BigFppfOver B S hS))).isTerminalObj
      (Sheaf.sheafifiedYoneda J)
  let eT : T ≅ ⊤_ (Sheaf J (Type (u + 1))) := hT.uniqueUpToIso terminalIsTerminal
  let i : X ⟶ ⊤_ (Sheaf J (Type (u + 1))) := terminal.from X
  have hA0 : IsPullback ((Sheaf.sheafifiedYoneda J).map p₁) ((Sheaf.sheafifiedYoneda J).map p₂)
      ((Sheaf.sheafifiedYoneda J).map (terminal.from U))
      ((Sheaf.sheafifiedYoneda J).map (terminal.from U)) := by
    simpa [p₁, p₂] using (Sheaf.sheafifiedYoneda J).map_isPullback
      (IsPullback.of_hasPullback (terminal.from U) (terminal.from U))
  have hA : IsPullback ((Sheaf.sheafifiedYoneda J).map p₁)
      ((Sheaf.sheafifiedYoneda J).map p₂) (fU ≫ i) (fU ≫ i) := by
    have hA1 : IsPullback ((Sheaf.sheafifiedYoneda J).map p₁)
        ((Sheaf.sheafifiedYoneda J).map p₂)
        ((Sheaf.sheafifiedYoneda J).map (terminal.from U) ≫ eT.hom)
        ((Sheaf.sheafifiedYoneda J).map (terminal.from U) ≫ eT.hom) :=
      hA0.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eT
        (by simp) (by simp) (by simp) (by simp)
    convert hA1 using 1 <;> exact terminalIsTerminal.hom_ext _ _
  obtain ⟨eR⟩ := nonempty_iso_pullback_of_isPullback_diag (A := (Sheaf.sheafifiedYoneda J).obj A)
    fU hA hpb
  have hRepr (V : BigFppfOver B S hS) :
      Nonempty (((Sheaf.sheafifiedYoneda J).obj V).obj ≅ (uliftYoneda.{u + 1}).obj V) :=
    ⟨((sheafToPresheaf J (Type (u + 1))).mapIso (eH.app V)).symm ≪≫
      J.uliftYonedaCompSheafToPresheaf.app V⟩
  exact ⟨U, R, (Sheaf.sheafifiedYoneda J).obj U, (Sheaf.sheafifiedYoneda J).obj R,
    hRepr U, hRepr R, ⟨fU, hfU, ⟨eR.hom, inferInstance⟩⟩⟩

/-- A directed colimit of affine fppf sheaves along thickenings satisfies the set-theoretic
condition if the coproduct of its stages is representable in the big site. -/
@[stacks 0AIS "colimit_condition"]
public theorem satisfiesSetTheoreticCondition_of_colimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : Nonempty (X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))))
    (hU : ∃ (U : BigFppfOver B S hS)
      (F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))),
      Nonempty (F.obj ≅ (uliftYoneda.{u + 1}).obj U) ∧
        Nonempty (F ≅ ∐ fun i : I ↦
          (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).obj
              ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := subcanonical_bigFppfOver_topology B S hS
  let K := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda J
  let eX : colimit K ≅ X := (Classical.choice hX).symm
  obtain ⟨U, F, hFU, hFC⟩ := hU
  let eFU : F.obj ≅ (uliftYoneda.{u + 1}).obj U := Classical.choice hFU
  let eFC : F ≅ ∐ fun i : I ↦ K.obj i := Classical.choice hFC
  let eH := uliftYonedaIsoSheafifiedYoneda J
  let eHU := eH.app U
  let eFH : F ≅ J.uliftYoneda.obj U :=
    (sheafificationIso F) ≪≫
      (presheafToSheaf J (Type (u + 1))).mapIso eFU ≪≫ eHU.symm
  let eUF : (Sheaf.sheafifiedYoneda J).obj U ≅ F := eHU.symm ≪≫ eFH.symm
  let fU : (Sheaf.sheafifiedYoneda J).obj U ⟶ X :=
    eUF.hom ≫ eFC.hom ≫ Sigma.desc (fun i => colimit.ι K i) ≫ eX.hom
  exact satisfiesSetTheoreticCondition_of_colimit_of_representable_epi B S hS D hD X hX U fU
    inferInstance

end AlgebraicGeometry.FormalSpace

end
