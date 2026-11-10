module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# The formal functions on an affine formal algebraic space are independent of the presentation

Let the fppf sheaf `X` over `S` be presented in two ways as a directed colimit of affine
schemes of the site along thickenings, say `X = colim_{i ∈ I₀} X_i = colim_{k ∈ I₁} Y_k`. Each
stage `X_i` is affine, hence quasi-compact, so the morphism `X_i → X` factors through some
stage `Y_k` of the other presentation, and symmetrically. Such a factorisation is unique,
because the colimit injections `Y_k → X` are monomorphisms and the sheafified Yoneda embedding
of the big affine fppf category is fully faithful. Pulling a compatible family of sections back
along a choice of factorisations therefore gives mutually inverse ring homomorphisms between
the two inverse limits `lim Γ(X_i, 𝒪)` and `lim Γ(Y_k, 𝒪)`.

The same factorisation argument shows that a morphism between stages of the two presentations
lying over `X` is itself a thickening, since it is a factor of a transition morphism of each
presentation. Surjectivity of the section projections therefore also passes between the two
presentations: a stage of one is a closed subscheme of a stage of the other, so its sections
are pulled back from there. This is the implication (4) ⇒ (5) of Stacks 0AIC, and with
`AlgebraicGeometry.FormalSpace.HasAllSurjectivePresentations.hasSomeSurjectivePresentation`
it makes conditions (4) and (5) equivalent.

## Main results

* `AlgebraicGeometry.FormalSpace.sectionsRingEquivOfPresentations`: the inverse limit of the
  rings of global sections of a presentation of an fppf sheaf by affine thickenings does not
  depend on the presentation.
* `AlgebraicGeometry.FormalSpace.surjective_sectionsRingEquivOfPresentations`: that
  comparison isomorphism is in particular surjective.
* `AlgebraicGeometry.FormalSpace.isThickening_of_factor_stage`: a morphism from a stage of one
  presentation to a stage of another which lies over the presented sheaf is a thickening.
* `AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_presentations`: if one
  presentation of a sheaf by affine thickenings has surjective section projections then so
  does every other.
* `AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation.hasAllSurjectivePresentations`:
  if some presentation of an affine formal algebraic space by affine thickenings has surjective
  section projections, then so does every presentation.
* `AlgebraicGeometry.FormalSpace.not_hasSomeSurjectivePresentation_of_presentation`: a single
  presentation with a non-surjective section projection refutes McQuillan's criterion.

## Implementation notes

The index of a presentation lives in `Type (u + 1)`, one universe above the schemes, so the
inverse limit of the section rings is not an object of `CommRingCat.{u}`: it is presented as
`CategoryTheory.Functor.sections` of the underlying set-valued diagram, a subtype of a product,
whose ring structure is `CategoryTheory.RingCat.sectionsSubring`, registered here as
`AlgebraicGeometry.FormalSpace.commRingSections`. The two comparison maps are therefore built
by hand, componentwise.

Both the compatibility of the pulled-back family and the fact that the two comparison maps are
mutually inverse reduce to one statement: two morphisms from a stage of one presentation into
stages of the other which induce the same morphism to the sheaf pull every element of the
inverse limit back to the same section. This holds because such morphisms become equal after
composing with a transition morphism into a common later stage — a factorisation of a morphism
to the sheaf through a stage is unique, the colimit injections being monomorphisms — and
elements of the inverse limit are invariant under transition maps.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

universe v w w₁ w₂

/-! ### Uniqueness of factorisations through a stage -/

/-- The ring homomorphism on rings of global sections induced by a morphism of the big affine
fppf category over `S`. -/
private abbrev stageΓ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} (φ : U ⟶ V) :
    Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj V)) ⟶
      Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj U)) :=
  Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map φ).op

/-- The ring homomorphism on rings of global sections induced by a morphism of the big affine
fppf category over `S`. -/
public abbrev stageΓ' (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} (φ : U ⟶ V) :
    Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj V)) ⟶
      Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj U)) :=
  Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map φ).op

/-- Taking global sections is contravariantly functorial. -/
private lemma stageΓ_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W : BigAffineFppf B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    stageΓ B S hS (a ≫ b) = stageΓ B S hS b ≫ stageΓ B S hS a := by
  change Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (a ≫ b)).op = _
  rw [(BigAffineFppf.toScheme B S hS).map_comp, op_comp, Scheme.Γ.map_comp]

/-- Pulling a global section back along a composite is pulling it back along each factor. -/
private lemma stageΓ_comp_apply (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W : BigAffineFppf B S hS} (a : U ⟶ V) (b : V ⟶ W)
    (x : Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj W))) :
    stageΓ B S hS (a ≫ b) x = stageΓ B S hS a (stageΓ B S hS b x) := by
  rw [stageΓ_comp, CommRingCat.comp_apply]

/-- Pulling global sections back along the identity is the identity. -/
private lemma stageΓ_id (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigAffineFppf B S hS} :
    stageΓ B S hS (𝟙 U) = 𝟙 (Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj U))) := by
  change Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (𝟙 U)).op = _
  rw [(BigAffineFppf.toScheme B S hS).map_id, op_id, Scheme.Γ.map_id]

/-- Pulling a global section back along the identity does nothing. -/
private lemma stageΓ_id_apply (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigAffineFppf B S hS}
    (x : Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj U))) :
    stageΓ B S hS (𝟙 U) x = x := by
  rw [stageΓ_id, ConcreteCategory.id_apply]

/-- Pulling a global section back along the identity does nothing. -/
public lemma stageΓ_id_apply' (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigAffineFppf B S hS}
    (x : Scheme.Γ.obj (op ((BigAffineFppf.toScheme B S hS).obj U))) :
    stageΓ' B S hS (𝟙 U) x = x :=
  stageΓ_id_apply B S hS x

/-- A morphism of the big affine fppf category over `S` whose underlying morphism of schemes is
a closed immersion represents a monomorphism of fppf sheaves. -/
private lemma mono_sheafifiedYoneda_inclusion_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} (φ : U ⟶ V)
    (hφ : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map φ)) :
    Mono ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map φ)) := by
  let : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
    ((BigAffineFppf.inclusion B S hS).map φ)) := hφ
  have hm : Mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map φ)) := inferInstance
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying (BigFppfOver.topology B S hS)
    (BigFppfOver.toScheme B S hS) ((BigAffineFppf.inclusion B S hS).map φ) hm

/-- The injection of a stage into the colimit of a directed presentation by affine thickenings
is a monomorphism, because every transition morphism of the presentation is a closed
immersion. -/
private lemma mono_colimit_ι_of_isThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (i : I) :
    Mono (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) :=
  Sheaf.mono_colimit_ι_of_mono_transition _
    (fun _ _ q => mono_sheafifiedYoneda_inclusion_map B S hS (D.map q) (hD q).1) i

/-- The transition morphisms of a presentation are compatible with the colimit injections. -/
private lemma sheafifiedYoneda_map_comp_colimit_ι_comp_inv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) {i i' : I} (t : i ⟶ i') :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.map t)) ≫
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i' ≫ e.inv =
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv := by
  exact colimit.w_assoc (D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) t _

/-- A morphism into a stage of a presentation by affine thickenings is determined by the
morphism to the presented sheaf that it induces: the colimit injection of the stage is a
monomorphism and the sheafified Yoneda embedding of the big affine fppf category is
faithful. -/
private theorem stage_hom_unique
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {U : BigAffineFppf B S hS} {k : I₁} (a b : U ⟶ D₁.obj k)
    (hab : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map a) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map b) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv) :
    a = b := by
  have : Mono (colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k) :=
    mono_colimit_ι_of_isThickening B S hS I₁ D₁ hD₁ k
  have hs : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map a) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map b) := by
    apply (cancel_mono (colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k)).1
    apply (cancel_mono e₁.inv).1
    simpa only [Category.assoc] using hab
  exact Functor.map_injective (F := BigAffineFppf.inclusion B S hS)
    (Functor.map_injective
      (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) hs)

/-- A morphism from a stage of one presentation to a sheaf factors through a stage of a
presentation by affine thickenings which is as late as we please. -/
private theorem exists_factor_above
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (V : BigAffineFppf B S hS)
    (y : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj V) ⟶ X) (i : I) :
    ∃ (m : I) (_ : i ≤ m) (c : V ⟶ D.obj m),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map c) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) m ≫ e.inv = y := by
  obtain ⟨n, c, hc⟩ := exists_factor_to_affine_stage B S hS X I D hD e V y
  obtain ⟨m, him, hnm⟩ := (inferInstance : IsDirected I (· ≤ ·)).directed i n
  exact ⟨m, him, c ≫ D.map (homOfLE hnm), by
    simp only [Functor.map_comp, Category.assoc,
      sheafifiedYoneda_map_comp_colimit_ι_comp_inv B S hS X I D e, hc]⟩

/-- Two morphisms between stages of two presentations lying over the same sheaf compose to a
transition morphism of the first presentation. -/
private theorem comp_eq_map_of_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {i m : I₀} {k : I₁} (u : i ⟶ m) (a : D₀.obj i ⟶ D₁.obj k) (b : D₁.obj k ⟶ D₀.obj m)
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map a) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv =
      colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv)
    (hb : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map b) ≫
        colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) m ≫ e₀.inv =
      colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv) :
    a ≫ b = D₀.map u := by
  apply stage_hom_unique B S hS X I₀ D₀ hD₀ e₀
  simp only [Functor.map_comp, Category.assoc, hb, ha,
    sheafifiedYoneda_map_comp_colimit_ι_comp_inv B S hS X I₀ D₀ e₀]

/-! ### A factoring morphism between stages is a thickening -/

/-- A morphism between stages of two presentations of the same fppf sheaf by affine
thickenings which lies over the sheaf is a thickening: composing it with a factorisation in
the other direction produces a transition morphism of each of the two presentations. -/
public theorem isThickening_of_factor_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (i : I₀) (k : I₁) (g : D₀.obj i ⟶ D₁.obj k)
    (hg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv =
      colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv) :
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map g) := by
  let G₀ := D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let G₁ := D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨m, hi, c', hc'⟩ := exists_factor_above B S hS X I₀ D₀ hD₀ e₀
    (D₁.obj k) (colimit.ι G₁ k ≫ e₁.inv) i
  obtain ⟨L, hkL, d', hd'⟩ := exists_factor_above B S hS X I₁ D₁ hD₁ e₁
    (D₀.obj m) (colimit.ι G₀ m ≫ e₀.inv) k
  have hgc : g ≫ c' = D₀.map (homOfLE hi) :=
    comp_eq_map_of_over B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ e₁ _ g c' hg hc'
  have hcd : c' ≫ d' = D₁.map (homOfLE hkL) :=
    comp_eq_map_of_over B S hS X I₁ D₁ hD₁ e₁ I₀ D₀ e₀ _ c' d' hc' hd'
  have hc'closed : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map c') := by
    have hcomp : IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map c' ≫
          (BigAffineFppf.toScheme B S hS).map d') := by
      have : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (c' ≫ d')) := by
        rw [hcd]
        exact (hD₁ _).1
      simpa only [Functor.map_comp] using this
    let : IsAffineHom ((BigAffineFppf.toScheme B S hS).map d') := inferInstance
    let : IsSeparated ((BigAffineFppf.toScheme B S hS).map d') := inferInstance
    exact IsClosedImmersion.of_comp
      (f := (BigAffineFppf.toScheme B S hS).map c')
      (g := (BigAffineFppf.toScheme B S hS).map d')
  have hgcclosed : IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map (g ≫ c')) := by
    rw [hgc]
    exact (hD₀ _).1
  have hgclosed : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map g) := by
    let : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map c') := hc'closed
    exact (IsClosedImmersion.comp_iff
      (f := (BigAffineFppf.toScheme B S hS).map g)
      (g := (BigAffineFppf.toScheme B S hS).map c')).mp hgcclosed
  have hgcsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map (g ≫ c')).base := by
    rw [hgc]
    exact (hD₀ _).2
  have hc'inj : Function.Injective
      ((BigAffineFppf.toScheme B S hS).map c').base := by
    let : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map c') := hc'closed
    exact (Scheme.Hom.isClosedEmbedding _).injective
  refine ⟨hgclosed, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hgcsurj (((BigAffineFppf.toScheme B S hS).map c').base y)
  refine ⟨x, ?_⟩
  apply hc'inj
  simpa [Scheme.Hom.comp_base] using hx

/-! ### The comparison of the two inverse limits of section rings -/

/-- The inverse limit of the rings of global sections of a presentation by affine schemes is a
commutative ring: it is the subring of the product of the stage rings cut out by compatibility
with the transition morphisms. -/
public instance commRingSections (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Category I] (D : I ⥤ BigAffineFppf B S hS) :
    CommRing (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections :=
  @Subring.toCommRing (∀ j, (sectionDiagram B S hS D).obj j) _
    (RingCat.sectionsSubring
      (sectionDiagram B S hS D ⋙ forget₂ CommRingCat RingCat.{u}))

/-- Two morphisms from a single affine scheme of the site into stages of a presentation by
affine thickenings which induce the same morphism to the presented sheaf pull every element of
the inverse limit of the section rings back to the same section. -/
private theorem stageΓ_apply_eq_of_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {U : BigAffineFppf B S hS}
    {y : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X}
    {k k' : I₁} (a : U ⟶ D₁.obj k) (b : U ⟶ D₁.obj k')
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map a) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv = y)
    (hb : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map b) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k' ≫ e₁.inv = y)
    (s : RingCat.sectionsSubring
      (sectionDiagram B S hS D₁ ⋙ forget₂ CommRingCat RingCat.{u})) :
    stageΓ B S hS a (s.val (op k)) = stageΓ B S hS b (s.val (op k')) := by
  obtain ⟨m, hkm, hk'm⟩ := (inferInstance : IsDirected I₁ (· ≤ ·)).directed k k'
  let p : k ⟶ m := homOfLE hkm
  let q : k' ⟶ m := homOfLE hk'm
  have key : a ≫ D₁.map p = b ≫ D₁.map q := by
    apply stage_hom_unique B S hS X I₁ D₁ hD₁ e₁
    simp only [Functor.map_comp, Category.assoc, ha, hb,
      sheafifiedYoneda_map_comp_colimit_ι_comp_inv B S hS X I₁ D₁ e₁]
  have hs := congrArg (fun φ => stageΓ B S hS φ (s.val (op m))) key
  simp only [stageΓ_comp_apply] at hs
  have hp : stageΓ B S hS (D₁.map p) (s.val (op m)) = s.val (op k) := s.property p.op
  have hq : stageΓ B S hS (D₁.map q) (s.val (op m)) = s.val (op k') := s.property q.op
  rw [hp, hq] at hs
  exact hs

/-- Two morphisms from a single affine scheme of the site into stages of a presentation by
affine thickenings which induce the same morphism to the presented sheaf pull every element of
the inverse limit of the section rings back to the same section. -/
public theorem stageΓ_apply_eq_of_over'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {U : BigAffineFppf B S hS}
    {y : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X}
    {k k' : I₁} (a : U ⟶ D₁.obj k) (b : U ⟶ D₁.obj k')
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map a) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv = y)
    (hb : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map b) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k' ≫ e₁.inv = y)
    (s : RingCat.sectionsSubring
      (sectionDiagram B S hS D₁ ⋙ forget₂ CommRingCat RingCat.{u})) :
    stageΓ' B S hS a (s.val (op k)) = stageΓ' B S hS b (s.val (op k')) :=
  stageΓ_apply_eq_of_over B S hS X I₁ D₁ hD₁ e₁ a b ha hb s

/-- Pulling sections back along a family of factorisations of the stages of one presentation
through the stages of another is a ring homomorphism between the inverse limits of the section
rings. -/
private def sectionsRingHomOfFactorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (idx : I₀ → I₁) (fac : ∀ i, D₀.obj i ⟶ D₁.obj (idx i))
    (hfac : ∀ i, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (fac i)) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (idx i) ≫ e₁.inv =
      colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv) :
    RingCat.sectionsSubring
        (sectionDiagram B S hS D₁ ⋙ forget₂ CommRingCat RingCat.{u}) →+*
      RingCat.sectionsSubring
        (sectionDiagram B S hS D₀ ⋙ forget₂ CommRingCat RingCat.{u}) where
  toFun s := ⟨fun m => stageΓ B S hS (fac m.unop) (s.val (op (idx m.unop))), by
    intro m m' f
    have key := stageΓ_apply_eq_of_over B S hS X I₁ D₁ hD₁ e₁
      (D₀.map f.unop ≫ fac m.unop) (fac m'.unop) (by
        simp only [Functor.map_comp, Category.assoc, hfac,
          sheafifiedYoneda_map_comp_colimit_ι_comp_inv B S hS X I₀ D₀ e₀]) (hfac m'.unop) s
    rw [stageΓ_comp_apply] at key
    exact key⟩
  map_one' := Subtype.ext <| funext fun m => map_one (stageΓ B S hS (fac m.unop)).hom
  map_mul' _ _ := Subtype.ext <| funext fun m => map_mul (stageΓ B S hS (fac m.unop)).hom _ _
  map_zero' := Subtype.ext <| funext fun m => map_zero (stageΓ B S hS (fac m.unop)).hom
  map_add' _ _ := Subtype.ext <| funext fun m => map_add (stageΓ B S hS (fac m.unop)).hom _ _

/-- Going through a stage of the second presentation and back is the identity on the inverse
limit of the section rings of the first: the round trip lies over the sheaf, as does the
identity of the stage, so it acts as a transition morphism, and sections are invariant under
transition morphisms. -/
private theorem sectionsRingHomOfFactorization_comp_apply
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (idx : I₀ → I₁) (fac : ∀ i, D₀.obj i ⟶ D₁.obj (idx i))
    (hfac : ∀ i, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (fac i)) ≫
        colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (idx i) ≫ e₁.inv =
      colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv)
    (jdx : I₁ → I₀) (gac : ∀ k, D₁.obj k ⟶ D₀.obj (jdx k))
    (hgac : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (gac k)) ≫
        colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (jdx k) ≫ e₀.inv =
      colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv)
    (s : RingCat.sectionsSubring
      (sectionDiagram B S hS D₁ ⋙ forget₂ CommRingCat RingCat.{u})) :
    sectionsRingHomOfFactorization B S hS X I₁ D₁ e₁ I₀ D₀ hD₀ e₀ jdx gac hgac
        (sectionsRingHomOfFactorization B S hS X I₀ D₀ e₀ I₁ D₁ hD₁ e₁ idx fac hfac s) = s := by
  apply Subtype.ext
  funext m
  change stageΓ B S hS (gac m.unop)
      (stageΓ B S hS (fac (jdx m.unop)) (s.val (op (idx (jdx m.unop))))) = s.val m
  rw [← stageΓ_comp_apply]
  have key := stageΓ_apply_eq_of_over B S hS X I₁ D₁ hD₁ e₁
    (y := colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) m.unop ≫ e₁.inv)
    (gac m.unop ≫ fac (jdx m.unop)) (𝟙 (D₁.obj m.unop))
    (by simp only [Functor.map_comp, Category.assoc, hfac, hgac]) (by simp) s
  rw [stageΓ_id_apply] at key
  rw [key]

/-- The inverse limit of the rings of global sections of a presentation of an fppf sheaf by
affine thickenings does not depend on the presentation: two such presentations of the same
sheaf have isomorphic limits. -/
@[no_expose] public def sectionsRingEquivOfPresentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    (sectionDiagram B S hS D₀ ⋙ forget CommRingCat.{u}).sections ≃+*
      (sectionDiagram B S hS D₁ ⋙ forget CommRingCat.{u}).sections := by
  classical
  choose idx fac hfac using fun i : I₀ =>
    exists_factor_to_affine_stage B S hS X I₁ D₁ hD₁ e₁ (D₀.obj i)
      (colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv)
  choose jdx gac hgac using fun k : I₁ =>
    exists_factor_to_affine_stage B S hS X I₀ D₀ hD₀ e₀ (D₁.obj k)
      (colimit.ι (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) k ≫ e₁.inv)
  exact
    { toFun := sectionsRingHomOfFactorization B S hS X I₁ D₁ e₁ I₀ D₀ hD₀ e₀ jdx gac hgac
      invFun := sectionsRingHomOfFactorization B S hS X I₀ D₀ e₀ I₁ D₁ hD₁ e₁ idx fac hfac
      left_inv := sectionsRingHomOfFactorization_comp_apply B S hS X I₁ D₁ hD₁ e₁ I₀ D₀ hD₀ e₀
        jdx gac hgac idx fac hfac
      right_inv := sectionsRingHomOfFactorization_comp_apply B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁
        idx fac hfac jdx gac hgac
      map_mul' := map_mul
        (sectionsRingHomOfFactorization B S hS X I₁ D₁ e₁ I₀ D₀ hD₀ e₀ jdx gac hgac)
      map_add' := map_add
        (sectionsRingHomOfFactorization B S hS X I₁ D₁ e₁ I₀ D₀ hD₀ e₀ jdx gac hgac) }

/-- The comparison isomorphism between the inverse limits of the section rings of two
presentations of the same fppf sheaf by affine thickenings is surjective. -/
public theorem surjective_sectionsRingEquivOfPresentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    Function.Surjective
      (sectionsRingEquivOfPresentations B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁) :=
  (sectionsRingEquivOfPresentations B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁).surjective

/-! ### McQuillan's criterion does not depend on the presentation -/

/-- Surjectivity of the projections from the inverse limit of the section rings onto the stage
rings passes from one presentation of an fppf sheaf by affine thickenings to any other: a stage
of the second presentation factors through a stage of the first by a thickening, hence by a
surjection on global sections, and the inverse limits are compared by pulling sections back
along such factorisations. -/
public theorem hasSurjectiveSectionProjections_of_presentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (I₁ : Type (u + 1)) [Preorder I₁] [Nonempty I₁] [IsDirected I₁ (· ≤ ·)]
    (D₁ : I₁ ⥤ BigAffineFppf B S hS)
    (hD₁ : ∀ ⦃i j : I₁⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₁.map f)))
    (e₁ : X ≅ colimit (D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (h₁ : HasSurjectiveSectionProjections B S hS D₁) :
    HasSurjectiveSectionProjections B S hS D₀ := by
  classical
  choose idx fac hfac using fun i : I₀ =>
    exists_factor_to_affine_stage B S hS X I₁ D₁ hD₁ e₁ (D₀.obj i)
      (colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e₀.inv)
  intro m y
  have hth : Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (fac m)) :=
    isThickening_of_factor_stage B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁ m (idx m) (fac m) (hfac m)
  obtain ⟨z, hz⟩ : ∃ z, stageΓ B S hS (fac m) z = y := by
    have haff : IsAffine ((BigAffineFppf.toScheme B S hS).obj (D₁.obj (idx m))) :=
      (D₁.obj (idx m)).property
    have hci : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (fac m)) := hth.1
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigAffineFppf.toScheme B S hS).map (fac m))).2 y
  obtain ⟨t, ht⟩ := h₁ (idx m) z
  refine ⟨sectionsRingHomOfFactorization B S hS X I₀ D₀ e₀ I₁ D₁ hD₁ e₁ idx fac hfac t, ?_⟩
  change stageΓ B S hS (fac m) (t.val (op (idx m))) = y
  rw [show t.val (op (idx m)) = z from ht, hz]

/-- If *some* presentation of an affine formal algebraic space by affine thickenings has all its
section-ring projections surjective, then *every* such presentation does. -/
@[stacks 0AIC "part (4) implies part (5)"]
public theorem HasSomeSurjectivePresentation.hasAllSurjectivePresentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasSomeSurjectivePresentation B S hS X) :
    HasAllSurjectivePresentations B S hS X := by
  obtain ⟨hAff, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨e₁⟩, h₁⟩ := hX
  let _ : Preorder I₁ := pre₁
  have _ : Nonempty I₁ := hne₁
  have _ : IsDirected I₁ (· ≤ ·) := hdir₁
  refine ⟨hAff, ?_⟩
  intro I₀ pre₀ hne₀ hdir₀ D₀ hD₀ he₀
  let _ : Preorder I₀ := pre₀
  obtain ⟨e₀⟩ := he₀
  exact hasSurjectiveSectionProjections_of_presentations B S hS X I₀ D₀ hD₀ e₀
    I₁ D₁ hD₁ e₁ h₁

/-- A single presentation of an fppf sheaf by affine thickenings with a non-surjective
section-ring projection refutes McQuillan's criterion, condition (4) of Stacks 0AIC, for that
sheaf: the condition is independent of the presentation. -/
public theorem not_hasSomeSurjectivePresentation_of_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS)
    (I₀ : Type (u + 1)) [Preorder I₀] [Nonempty I₀] [IsDirected I₀ (· ≤ ·)]
    (D₀ : I₀ ⥤ BigAffineFppf B S hS)
    (hD₀ : ∀ ⦃i j : I₀⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D₀.map f)))
    (e₀ : X ≅ colimit (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (h₀ : ¬ HasSurjectiveSectionProjections B S hS D₀) :
    ¬ HasSomeSurjectivePresentation B S hS X := by
  intro hX
  obtain ⟨-, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨e₁⟩, h₁⟩ := hX
  let _ : Preorder I₁ := pre₁
  have _ : Nonempty I₁ := hne₁
  have _ : IsDirected I₁ (· ≤ ·) := hdir₁
  exact h₀ (hasSurjectiveSectionProjections_of_presentations B S hS X I₀ D₀ hD₀ e₀
    I₁ D₁ hD₁ e₁ h₁)

end AlgebraicGeometry.FormalSpace

end
