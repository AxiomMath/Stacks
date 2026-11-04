module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDirectImagePasting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pasting the derived base change comparison along the direct image legs

Let

```
A₀ --U₀--> B₀
|P₁         |P₁'
v           v
A₁ --U₁--> B₁
|P₂         |P₂'
v           v
A₂ --U₂--> B₂
```

be two vertically composable commutative squares of additive functors between abelian
categories, with the **horizontal** functors `U₁`, `U₂` exact and the **vertical** ones
arbitrary, together with comparisons `cP : P₁ ⋙ P₂ ≅ P` and `cP' : P₁' ⋙ P₂' ≅ P'` of the two
composite vertical legs. This file proves that the descent
`Stacks.Cohomology.BaseChange.derived` of the comparison of the outer rectangle to the bounded
below derived categories is the composite of the descents of the two squares, read through the
comparisons `RP₁ ⋙ RP₂ ≅ RP` and `RP₁' ⋙ RP₂' ≅ RP'` of the derived vertical legs.

This is the direction of pasting that the integral-base steps of [Stacks, Tag 0F02] need, and
the direction that was missing at the derived level. What the library had,
`Stacks.Cohomology.BaseChange.derived_eq_derivedPaste`, composes two squares **horizontally**,
i.e. along the exact legs; its comparisons of composite legs are
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, which exists because an exact
functor makes every object right acyclic. Composing along the *vertical* legs needs the
composition isomorphism for a first factor that is not exact but **preserves injective
objects** — [Stacks, Tag 015M] in the form
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` — and that is the only hypothesis added
here: `P₁` and `P₁'` preserve injective objects.

The underived input is exactly the underived pasting identity, evaluated at each object. On the
small étale sites of schemes that identity is
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_pasteDirectImage_app`, so the étale corollary at
the end of the file,
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste`, has no hypothesis
beyond the commutativity of the two squares: direct image of abelian sheaves on a small étale
site preserves injective objects
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects`) for *every*
morphism of schemes, with no integrality, finiteness or torsion assumption.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives`: the comparison
  `RF ⋙ RG ≅ RH` attached to an isomorphism `F ⋙ G ≅ H` with `F` preserving injective objects.
  It is the non-exact counterpart of
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, with the same characterizing
  factorization.
* `Stacks.Cohomology.BaseChange.derivedVPaste`: the vertically pasted derived comparison.
* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso'`: the comparison
  `Ra_* ⋙ Rb_* ≅ R(ab)_*` with the composite carried as a named morphism.

## Main results

* `Stacks.Cohomology.BaseChange.mapPlus_vPaste_app`: the degreewise pasting identity on bounded
  below homotopy categories.
* `Stacks.Cohomology.BaseChange.derived_eq_derivedVPaste` and
  `Stacks.Cohomology.BaseChange.derived_eq_derivedVPaste_app`: **the pasting law for the derived
  comparison along the non-exact legs**, as an identity of natural transformations and evaluated
  at an object.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste` and
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`: the étale
  instance.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_isIso_derivedVPaste`: two out
  of three for the étale instance.

## Implementation notes

*What is still missing for the degreewise form.* [Stacks, Tag 0F04] and [Stacks, Tag 0F05] need
the degree-`q` cohomology of the law proved here, read through the relative Leray identification
`Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral` of
`BaseChangeHigher/IntegralRelativeLeray.lean`. Two things stand between the two statements, and
neither is proved here.

* The descent through `Stacks.EtaleCohomology.baseChangeSourceIso` and
  `Stacks.EtaleCohomology.baseChangeTargetIso`, which is what
  `BaseChangeHigher/SmallEtaleHigherBaseChangePasting.lean` does for the horizontal law.
* The identification of `Stacks.DerivedIndexing.rightDerivedPlusEdge` at
  `smallEtalePushforwardAb π` and `smallEtalePushforwardAb g` with
  `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral π g`, which is what carries the
  comparison between the injective-resolution convention
  `CategoryTheory.Functor.rightDerived n` and the cohomology of `rightDerivedFunctorPlus`.
  `Stacks.DerivedIndexing.rightDerivedIso` and
  `Stacks.DerivedIndexing.edge_comp_rightDerivedIso` are the generic halves of it.

*No tag is placed.* [Stacks, Tag 0E46] is the derived pasting law for ringed topoi and sheaves of
modules, formalized as `Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_comp`;
[Stacks, Tag 0E47] is its horizontal companion. What is proved here is the bounded-below
abelian form of the vertical law, an input to the degreewise statements of [Stacks, Tag 0F04]
and [Stacks, Tag 0F05] rather than the statement of any tag.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe w w' w'' v v' v'' u u' u''

namespace Stacks.Cohomology.BaseChange

/-! ### Reassociation in an arbitrary category

The three rearrangements the chases below run on. They are stated on variables in a single
abstract category: the morphisms they are applied to are components of comparisons of right
derived functors, whose sources and targets agree only definitionally — `(F ⋙ G).mapHᴷ.obj K`
against `G.mapHᴷ.obj (F.mapHᴷ.obj K)` — so a `rw`-driven rearrangement at those types builds
ill-typed terms, while a term-level application checks the definitional equality once. -/

section Reassoc3

variable {𝒞 : Type*} [Category* 𝒞]

/-- A functor applied to a fourfold composite. -/
theorem mapComp₄ {𝒟 : Type*} [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟) {X₀ X₁ X₂ X₃ X₄ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    Φ.map a ≫ Φ.map b ≫ Φ.map c ≫ Φ.map d = Φ.map (a ≫ b ≫ c ≫ d) := by simp

/-- **A characterizing factorization solved for the inverses of its two invertible factors.**
Only `h₁` and `p` are inverted; nothing else is assumed invertible. -/
theorem invFacAux {A B C D : 𝒞} (a : A ⟶ B) {h₁ : B ⟶ C} {h₂ : C ⟶ B} {p : A ⟶ D} {p' : D ⟶ A}
    {u : D ⟶ C} (hh : h₁ ≫ h₂ = 𝟙 B) (hp : p' ≫ p = 𝟙 D) (h : a ≫ h₁ = p ≫ u) :
    u ≫ h₂ = p' ≫ a := by
  calc u ≫ h₂ = (𝟙 D ≫ u) ≫ h₂ := by simp
    _ = (p' ≫ p ≫ u) ≫ h₂ := by rw [← hp]; simp
    _ = (p' ≫ a ≫ h₁) ≫ h₂ := by rw [h]
    _ = p' ≫ a ≫ h₁ ≫ h₂ := by simp
    _ = p' ≫ a := by rw [hh]; simp

/-- **The shape of the target-side chase of the vertical pasting law.** -/
theorem vTargetChase {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ W₁ Z₁ V₁ : 𝒞}
    {u : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄} {ee : X₄ ⟶ X₅}
    {p : X₁ ⟶ Y₁} {r : Y₁ ⟶ Y₂} {s : Y₂ ⟶ X₄}
    {qq : X₀ ⟶ W₁} {m : W₁ ⟶ Y₁} {n : Y₂ ⟶ Z₁} {z : Z₁ ⟶ X₅}
    {zz : W₁ ⟶ V₁} {ww : V₁ ⟶ Z₁}
    (h1 : b ≫ c ≫ d = p ≫ r ≫ s) (h2 : qq ≫ m = u ≫ p) (h3 : s ≫ ee = n ≫ z)
    (h4 : m ≫ r ≫ n = zz ≫ ww) :
    u ≫ b ≫ c ≫ d ≫ ee = qq ≫ zz ≫ ww ≫ z := by
  calc u ≫ b ≫ c ≫ d ≫ ee = u ≫ (b ≫ c ≫ d) ≫ ee := by simp
    _ = u ≫ (p ≫ r ≫ s) ≫ ee := by rw [h1]
    _ = (u ≫ p) ≫ r ≫ (s ≫ ee) := by simp
    _ = (qq ≫ m) ≫ r ≫ (n ≫ z) := by rw [← h2, h3]
    _ = qq ≫ (m ≫ r ≫ n) ≫ z := by simp
    _ = qq ≫ (zz ≫ ww) ≫ z := by rw [h4]
    _ = qq ≫ zz ≫ ww ≫ z := by simp

/-- **The shape of the main chase of the vertical pasting law.** -/
theorem vMainChase {X₀ X₁ X₂ X₃ X₄ X₅ M₁ M₂ T₁ E₁ E₂ E₃ F₁ G₁ G₂ G₃ : 𝒞}
    {a₀ : X₀ ⟶ X₁} {a₁ : X₁ ⟶ X₂} {a₂ : X₂ ⟶ X₃} {a₃ : X₃ ⟶ X₄} {a₄ : X₄ ⟶ X₅}
    {m₁ : X₀ ⟶ M₁} {m₂ : M₁ ⟶ M₂} {m₃ : M₂ ⟶ X₂} {t₂ : M₂ ⟶ T₁} {t₃ : T₁ ⟶ X₃}
    {e₁ : M₁ ⟶ E₁} {e₂ : E₁ ⟶ E₂} {e₃ : E₂ ⟶ E₃} {e₄ : E₃ ⟶ T₁}
    {f₁ : X₀ ⟶ F₁} {f₂ : F₁ ⟶ E₁}
    {g₁ : E₂ ⟶ G₁} {g₂ : G₁ ⟶ G₂} {g₃ : G₂ ⟶ G₃} {g₄ : G₃ ⟶ X₅} {q : F₁ ⟶ G₂}
    (hA : a₀ ≫ a₁ = m₁ ≫ m₂ ≫ m₃) (hn2 : m₃ ≫ a₂ = t₂ ≫ t₃)
    (hf2 : m₂ ≫ t₂ = e₁ ≫ e₂ ≫ e₃ ≫ e₄) (hnU : m₁ ≫ e₁ = f₁ ≫ f₂)
    (htail : e₃ ≫ e₄ ≫ t₃ ≫ a₃ ≫ a₄ = g₁ ≫ g₂ ≫ g₃ ≫ g₄)
    (hdeg : f₂ ≫ e₂ ≫ g₁ ≫ g₂ = q) :
    a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ = f₁ ≫ q ≫ g₃ ≫ g₄ := by
  calc a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ = (a₀ ≫ a₁) ≫ a₂ ≫ a₃ ≫ a₄ := by simp
    _ = (m₁ ≫ m₂ ≫ m₃) ≫ a₂ ≫ a₃ ≫ a₄ := by rw [hA]
    _ = m₁ ≫ m₂ ≫ (m₃ ≫ a₂) ≫ a₃ ≫ a₄ := by simp
    _ = m₁ ≫ m₂ ≫ (t₂ ≫ t₃) ≫ a₃ ≫ a₄ := by rw [hn2]
    _ = m₁ ≫ (m₂ ≫ t₂) ≫ t₃ ≫ a₃ ≫ a₄ := by simp
    _ = m₁ ≫ (e₁ ≫ e₂ ≫ e₃ ≫ e₄) ≫ t₃ ≫ a₃ ≫ a₄ := by rw [hf2]
    _ = (m₁ ≫ e₁) ≫ e₂ ≫ (e₃ ≫ e₄ ≫ t₃ ≫ a₃ ≫ a₄) := by simp
    _ = (f₁ ≫ f₂) ≫ e₂ ≫ (g₁ ≫ g₂ ≫ g₃ ≫ g₄) := by rw [hnU, htail]
    _ = f₁ ≫ (f₂ ≫ e₂ ≫ g₁ ≫ g₂) ≫ g₃ ≫ g₄ := by simp
    _ = f₁ ≫ q ≫ g₃ ≫ g₄ := by rw [hdeg]

end Reassoc3

end Stacks.Cohomology.BaseChange

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The composition comparison for a first factor preserving injective objects -/

section PreservesInjectivesComposition

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesInjectiveObjects]
  (e : F ⋙ G ≅ H)

/-- **The comparison `RF ⋙ RG ≅ RH` for `F` preserving injective objects and
`e : F ⋙ G ≅ H`.** A functor preserving injective objects carries an injective object to one
right acyclic for any additive `G`
(`CategoryTheory.Functor.rightAcyclic_obj_of_preservesInjectiveObjects`), so the acyclicity
hypothesis of [Stacks, Tag 015M] holds and the resulting isomorphism `R(G ∘ F) ≅ RF ⋙ RG` is
transported along `e` by the invariance of right derivation.

This is the counterpart of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, in which the *second* factor is
assumed exact instead. The two are the two ways the acyclicity hypothesis of [Stacks, Tag 015M]
is met, and they are the comparisons the two directions of pasting the derived base change
comparison consume. -/
@[sga "4 V 2.2" "more general"]
def rightDerivedFunctorPlusCompIsoOfPreservesInjectives :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
      (fun I hI => rightAcyclic_obj_of_preservesInjectiveObjects F G I hI)).symm ≪≫
    rightDerivedFunctorPlusNatIso e

/-- `rightDerivedFunctorPlusCompIsoOfPreservesInjectives` unfolded, so that the canonical
comparison transformation and the invariance comparison can be handled separately. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom :
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G H e).hom =
      (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
          (fun I hI => rightAcyclic_obj_of_preservesInjectiveObjects F G I hI)).inv ≫
        (rightDerivedFunctorPlusNatIso e).hom := rfl

/-- **The characterizing factorization of
`rightDerivedFunctorPlusCompIsoOfPreservesInjectives`.** On a bounded below complex `N`, the
derived-functor unit of `RG` at `F(N)` followed by `RG` of the derived-functor unit of `RF` at
`N` and then by the comparison is the degreewise comparison `e` followed by the derived-functor
unit of `RH`.

Since `RH` is a right derived functor with that unit, this determines the comparison. The proof
is that of `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac`, with the
acyclicity witness replaced. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_fac (N : HomotopyCategory.Plus A) :
    G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj N) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app N) ≫
          (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G H e).hom.app
            (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app N) ≫
        H.rightDerivedFunctorPlusUnit.app N := by
  have hhom : (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
      (fun I hI => rightAcyclic_obj_of_preservesInjectiveObjects F G I hI)).hom =
      rightDerivedFunctorPlusComp F G := rfl
  have h1 : G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj N) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app N) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnit.app N ≫
          (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
            (fun I hI => rightAcyclic_obj_of_preservesInjectiveObjects F G I hI)).hom.app
              (DerivedCategory.Plus.Qh.obj N) := by
    rw [hhom, rightDerivedFunctorPlusComp_fac_app F G N, ← Category.assoc,
      ← DerivedCategory.Plus.Qh.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h2 := rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
    H.rightDerivedFunctorPlus (F ⋙ G).rightDerivedFunctorPlusUnit
    H.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso A)
    (isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).hom N
  have h3 : (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N ≫
      (mapHomotopyCategoryPlusNatIso e).hom.app N =
      (mapHomotopyCategoryPlusCompIso e).hom.app N := by
    rw [mapHomotopyCategoryPlusNatIso_hom]
    exact Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_hom_comp
      (Stacks.Cohomology.BaseChange.mapPlus e.hom |>.app N)
  rw [rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom, NatTrans.comp_app,
    ← Category.assoc, ← Category.assoc, h1]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, rightDerivedFunctorPlusNatIso, rightDerivedNatIso_hom, h2,
    ← Category.assoc, isoWhiskerRight_hom, Functor.whiskerRight_app,
    ← DerivedCategory.Plus.Qh.map_comp, h3]

/-- **The characterizing factorization, solved for the inverse of the comparison.** The
comparison of the composite *source* legs enters the descent along the derived-functor unit
contravariantly, and this is the form that descent consumes. Only the comparison itself and the
degreewise comparison are inverted; no derived-functor unit is assumed invertible. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_inv_fac
    (N : HomotopyCategory.Plus A) :
    H.rightDerivedFunctorPlusUnit.app N ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G H e).inv.app
          (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).inv.app N) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj N) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app N) := by
  have hp : DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).inv.app N) ≫
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app N) =
      𝟙 (DerivedCategory.Plus.Qh.obj (H.mapHomotopyCategoryPlus.obj N)) := by
    rw [← DerivedCategory.Plus.Qh.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  exact Stacks.Cohomology.BaseChange.invFacAux
    (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj N) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app N))
    ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G H e).hom_inv_id_app _) hp
    ((Category.assoc _ _ _).trans
      (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_fac F G H e N))

end PreservesInjectivesComposition

end CategoryTheory.Functor

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The degreewise vertical pasting identity -/

section VPasteComplexes

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Preadditive A₀] [Preadditive A₁] [Preadditive A₂]
  [Preadditive B₀] [Preadditive B₁] [Preadditive B₂]
  {P₁ : A₀ ⥤ A₁} {P₂ : A₁ ⥤ A₂} {P : A₀ ⥤ A₂}
  {P₁' : B₀ ⥤ B₁} {P₂' : B₁ ⥤ B₂} {P' : B₀ ⥤ B₂}
  {U₀ : A₀ ⥤ B₀} {U₁ : A₁ ⥤ B₁} {U₂ : A₂ ⥤ B₂}
  [P₁.Additive] [P₂.Additive] [P.Additive]
  [P₁'.Additive] [P₂'.Additive] [P'.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  (cP : P₁ ⋙ P₂ ≅ P) (cP' : P₁' ⋙ P₂' ≅ P')
  (τ : P ⋙ U₂ ⟶ U₀ ⋙ P') (τ₁ : P₁ ⋙ U₁ ⟶ U₀ ⋙ P₁') (τ₂ : P₂ ⋙ U₂ ⟶ U₁ ⋙ P₂')

/-- **A vertical pasting identity between squares of additive functors, applied degreewise to a
complex.** The hypothesis is the pasting identity at each object of the source category; the
conclusion is the same identity for the induced transformations on complexes, where it holds in
every degree by the hypothesis. -/
theorem vPaste_mapHomologicalComplex_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (L : HomologicalComplex A₀ c) :
    (NatTrans.mapHomologicalComplex τ c).app L =
      (U₂.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cP.inv c).app L) ≫
        (NatTrans.mapHomologicalComplex τ₂ c).app ((P₁.mapHomologicalComplex c).obj L) ≫
          (P₂'.mapHomologicalComplex c).map
              ((NatTrans.mapHomologicalComplex τ₁ c).app L) ≫
            (NatTrans.mapHomologicalComplex cP'.hom c).app
              ((U₀.mapHomologicalComplex c).obj L) := by
  ext i
  simpa using hτ (L.X i)

/-- **The vertical pasting identity on the homotopy category.** The image of
`vPaste_mapHomologicalComplex_app` under the quotient by homotopy. -/
theorem vPaste_mapHomotopyCategory_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (M : HomotopyCategory A₀ c) :
    (NatTrans.mapHomotopyCategory τ c).app M =
      (U₂.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory cP.inv c).app M) ≫
        (NatTrans.mapHomotopyCategory τ₂ c).app ((P₁.mapHomotopyCategory c).obj M) ≫
          (P₂'.mapHomotopyCategory c).map
              ((NatTrans.mapHomotopyCategory τ₁ c).app M) ≫
            (NatTrans.mapHomotopyCategory cP'.hom c).app
              ((U₀.mapHomotopyCategory c).obj M) := by
  obtain ⟨L⟩ := M
  refine Eq.trans (congrArg (fun z => (HomotopyCategory.quotient B₂ c).map z)
    (vPaste_mapHomologicalComplex_app cP cP' τ τ₁ τ₂ c hτ L)) ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

end VPasteComplexes

section VPastePlus

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  (P₁ : A₀ ⥤ A₁) (P₂ : A₁ ⥤ A₂) (P : A₀ ⥤ A₂)
  (P₁' : B₀ ⥤ B₁) (P₂' : B₁ ⥤ B₂) (P' : B₀ ⥤ B₂)
  (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
  [P₁.Additive] [P₂.Additive] [P.Additive]
  [P₁'.Additive] [P₂'.Additive] [P'.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  (cP : P₁ ⋙ P₂ ≅ P) (cP' : P₁' ⋙ P₂' ≅ P')
  (τ : P ⋙ U₂ ⟶ U₀ ⋙ P') (τ₁ : P₁ ⋙ U₁ ⟶ U₀ ⋙ P₁') (τ₂ : P₂ ⋙ U₂ ⟶ U₁ ⋙ P₂')

/-- **The degreewise image on `HomotopyCategory.Plus` of a vertical pasting identity between
squares of additive functors is the pasting of the degreewise images.** The two comparisons `cP`
and `cP'` of the composite vertical legs are replaced by their degreewise images under
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`, and nothing else changes.

The hypothesis is exactly the underived vertical pasting identity evaluated at each object,
which is the form in which
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_pasteDirectImage_app` is proved. -/
theorem mapPlus_vPaste_app
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (K : HomotopyCategory.Plus A₀) :
    (mapPlus τ).app K =
      U₂.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso cP).inv.app K) ≫
        (mapPlus τ₂).app (P₁.mapHomotopyCategoryPlus.obj K) ≫
          P₂'.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
            (Functor.mapHomotopyCategoryPlusCompIso cP').hom.app
              (U₀.mapHomotopyCategoryPlus.obj K) := by
  ext
  exact vPaste_mapHomotopyCategory_app cP cP' τ τ₁ τ₂ (ComplexShape.up ℤ) hτ K.obj

end VPastePlus

/-! ### The target side of the vertical pasting law -/

section VTarget

variable {A₀ A₁ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [EnoughInjectives A₀] [EnoughInjectives A₁]
  [EnoughInjectives B₀] [EnoughInjectives B₁]
  (P₁ : A₀ ⥤ A₁) (P₁' : B₀ ⥤ B₁) (P₂' : B₁ ⥤ B₂) (P' : B₀ ⥤ B₂)
  (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁)
  [P₁.Additive] [P₁'.Additive] [P₂'.Additive] [P'.Additive]
  [U₀.Additive] [U₁.Additive]
  [P₁'.PreservesInjectiveObjects]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  (cP' : P₁' ⋙ P₂' ≅ P') (τ₁ : P₁ ⋙ U₁ ⟶ U₀ ⋙ P₁')

/-- **The target side of the vertical pasting law.** The derived-functor unit of `RU₁` cancels
against the comparison descending the upper square, the unit of `RP₂'` moves the degreewise
comparison of that square out, and what is left is the characterizing factorization of the
comparison of the derived composite target leg. -/
theorem derivedVPaste_target_fac (K : HomotopyCategory.Plus A₀) :
    P₂'.rightDerivedFunctorPlusUnit.app
          (U₁.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K)) ≫
        P₂'.rightDerivedFunctorPlus.map
            (U₁.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
          P₂'.rightDerivedFunctorPlus.map
              (U₁.rightDerivedFunctorPlus.map (P₁.rightDerivedFunctorPlusUnit.app K)) ≫
            P₂'.rightDerivedFunctorPlus.map
                ((derived P₁ P₁' U₁ U₀ τ₁
                  (asIso U₁.rightDerivedFunctorPlusUnit)).app
                    (DerivedCategory.Plus.Qh.obj K)) ≫
              (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
                  P₁' P₂' P' cP').hom.app
                (U₀.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          (P₂'.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K)) ≫
        DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso cP').hom.app
              (U₀.mapHomotopyCategoryPlus.obj K)) ≫
          P'.rightDerivedFunctorPlusUnit.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
            P'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnit.app K) := by
  have hinner : U₁.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K) ≫
      U₁.rightDerivedFunctorPlus.map (P₁.rightDerivedFunctorPlusUnit.app K) ≫
        (derived P₁ P₁' U₁ U₀ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app
          (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K) ≫
        P₁'.rightDerivedFunctorPlusUnit.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
          P₁'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnit.app K) := by
    rw [derived_fac_app, onHomotopy_app]
    exact (asIso U₁.rightDerivedFunctorPlusUnit).hom_inv_id_app_assoc _ _
  have h1 : P₂'.rightDerivedFunctorPlus.map
        (U₁.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
      P₂'.rightDerivedFunctorPlus.map
          (U₁.rightDerivedFunctorPlus.map (P₁.rightDerivedFunctorPlusUnit.app K)) ≫
        P₂'.rightDerivedFunctorPlus.map
          ((derived P₁ P₁' U₁ U₀ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app
            (DerivedCategory.Plus.Qh.obj K)) =
      P₂'.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K)) ≫
        P₂'.rightDerivedFunctorPlus.map
            (P₁'.rightDerivedFunctorPlusUnit.app (U₀.mapHomotopyCategoryPlus.obj K)) ≫
          P₂'.rightDerivedFunctorPlus.map
            (P₁'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnit.app K)) := by
    refine (mapComp₃ P₂'.rightDerivedFunctorPlus _ _ _).trans ?_
    refine Eq.trans (congrArg P₂'.rightDerivedFunctorPlus.map hinner) ?_
    exact (mapComp₃ P₂'.rightDerivedFunctorPlus _ _ _).symm
  exact vTargetChase h1
    (P₂'.rightDerivedFunctorPlusUnit.naturality ((mapPlus τ₁).app K))
    ((Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives P₁' P₂' P' cP').hom.naturality
      (U₀.rightDerivedFunctorPlusUnit.app K))
    (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_fac
      P₁' P₂' P' cP' (U₀.mapHomotopyCategoryPlus.obj K))

end VTarget

/-! ### The vertically pasted derived comparison -/

section VPaste

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives A₂]
  [EnoughInjectives B₀] [EnoughInjectives B₁]
  (P₁ : A₀ ⥤ A₁) (P₂ : A₁ ⥤ A₂) (P : A₀ ⥤ A₂)
  (P₁' : B₀ ⥤ B₁) (P₂' : B₁ ⥤ B₂) (P' : B₀ ⥤ B₂)
  (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
  [P₁.Additive] [P₂.Additive] [P.Additive]
  [P₁'.Additive] [P₂'.Additive] [P'.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [P₁.PreservesInjectiveObjects] [P₁'.PreservesInjectiveObjects]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  (cP : P₁ ⋙ P₂ ≅ P) (cP' : P₁' ⋙ P₂' ≅ P')
  (τ : P ⋙ U₂ ⟶ U₀ ⋙ P') (τ₁ : P₁ ⋙ U₁ ⟶ U₀ ⋙ P₁') (τ₂ : P₂ ⋙ U₂ ⟶ U₁ ⋙ P₂')

/-- **The vertically pasted derived comparison**: the derived comparisons of the two squares,
read through the comparisons of the derived composite vertical legs. -/
def derivedVPaste :
    P.rightDerivedFunctorPlus ⋙ U₂.rightDerivedFunctorPlus ⟶
      U₀.rightDerivedFunctorPlus ⋙ P'.rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives P₁ P₂ P cP).inv
      U₂.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft P₁.rightDerivedFunctorPlus
      (derived P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derived P₁ P₁' U₁ U₀ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit))
      P₂'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft U₀.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives P₁' P₂' P' cP').hom

/-- The components of `Stacks.Cohomology.BaseChange.derivedVPaste`. -/
theorem derivedVPaste_app (M : DerivedCategory.Plus A₀) :
    (derivedVPaste P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ₁ τ₂).app M =
      U₂.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
            P₁ P₂ P cP).inv.app M) ≫
        (derived P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).app
            (P₁.rightDerivedFunctorPlus.obj M) ≫
          P₂'.rightDerivedFunctorPlus.map
              ((derived P₁ P₁' U₁ U₀ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app M) ≫
            (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
                P₁' P₂' P' cP').hom.app
              (U₀.rightDerivedFunctorPlus.obj M) := by
  simp only [derivedVPaste, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator, Category.id_comp]

/-- The computation the descent of the vertical pasting law reduces to: after the derived-functor
unit of `RP`, the vertically pasted derived comparison is the `onHomotopy` of the outer
rectangle. -/
theorem unit_comp_derivedVPaste_app
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (K : HomotopyCategory.Plus A₀) :
    U₂.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlusUnit.app K) ≫
        (derivedVPaste P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ₁ τ₂).app
          (DerivedCategory.Plus.Qh.obj K) =
      (onHomotopy P P' U₂ U₀ τ (asIso U₂.rightDerivedFunctorPlusUnit)).app K := by
  have hA : U₂.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlusUnit.app K) ≫
      U₂.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives P₁ P₂ P cP).inv.app
          (DerivedCategory.Plus.Qh.obj K)) =
      U₂.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso cP).inv.app K)) ≫
        U₂.rightDerivedFunctorPlus.map
            (P₂.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
          U₂.rightDerivedFunctorPlus.map
            (P₂.rightDerivedFunctorPlus.map (P₁.rightDerivedFunctorPlusUnit.app K)) := by
    simp only [← Functor.map_comp,
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_inv_fac P₁ P₂ P cP K]
  have hfac2 : U₂.rightDerivedFunctorPlus.map
        (P₂.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
      (derived P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).app
        (DerivedCategory.Plus.Qh.obj (P₁.mapHomotopyCategoryPlus.obj K)) =
      (asIso U₂.rightDerivedFunctorPlusUnit).inv.app
          (P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map
            ((mapPlus τ₂).app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
          P₂'.rightDerivedFunctorPlusUnit.app
              (U₁.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K)) ≫
            P₂'.rightDerivedFunctorPlus.map
              (U₁.rightDerivedFunctorPlusUnit.app (P₁.mapHomotopyCategoryPlus.obj K)) :=
    (derived_fac_app P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)
        (P₁.mapHomotopyCategoryPlus.obj K)).trans
      (onHomotopy_app P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)
        (P₁.mapHomotopyCategoryPlus.obj K))
  have hdeg : DerivedCategory.Plus.Qh.map
        (U₂.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso cP).inv.app K)) ≫
      DerivedCategory.Plus.Qh.map ((mapPlus τ₂).app (P₁.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map
            (P₂'.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K)) ≫
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso cP').hom.app
              (U₀.mapHomotopyCategoryPlus.obj K)) =
      DerivedCategory.Plus.Qh.map ((mapPlus τ).app K) := by
    refine (mapComp₄ DerivedCategory.Plus.Qh _ _ _ _).trans ?_
    exact congrArg DerivedCategory.Plus.Qh.map
      (mapPlus_vPaste_app P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ τ₁ τ₂ hτ K).symm
  rw [derivedVPaste_app]
  exact (vMainChase hA
    ((derived P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).naturality
      (P₁.rightDerivedFunctorPlusUnit.app K))
    hfac2
    ((asIso U₂.rightDerivedFunctorPlusUnit).inv.naturality
      ((Functor.mapHomotopyCategoryPlusCompIso cP).inv.app K))
    (derivedVPaste_target_fac P₁ P₁' P₂' P' U₀ U₁ cP' τ₁ K)
    hdeg).trans
    (onHomotopy_app P P' U₂ U₀ τ (asIso U₂.rightDerivedFunctorPlusUnit) K).symm

/-- The identity the descent of the vertical pasting law is proved from: both sides have the
same composite with the derived-functor unit of `RP`. -/
theorem unit_comp_derived_eq_derivedVPaste_app
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (K : HomotopyCategory.Plus A₀) :
    (compUnit P U₂).app K ≫
        (derived P P' U₂ U₀ τ (asIso U₂.rightDerivedFunctorPlusUnit)).app
          (DerivedCategory.Plus.Qh.obj K) =
      (compUnit P U₂).app K ≫
        (derivedVPaste P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ₁ τ₂).app
          (DerivedCategory.Plus.Qh.obj K) := by
  rw [compUnit_app, derived_fac_app]
  exact (unit_comp_derivedVPaste_app P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ τ₁ τ₂ hτ K).symm

/-- **The vertical pasting law for the derived base change comparison.** For two vertically
composable commutative squares of additive functors with exact horizontal legs and with first
vertical legs preserving injective objects, the descent of the comparison of the outer rectangle
is the composite of the descents of the two squares, read through the comparisons of the derived
composite vertical legs.

The hypothesis is exactly the underived vertical pasting identity, evaluated at each object. -/
theorem derived_eq_derivedVPaste
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X)) :
    derived P P' U₂ U₀ τ (asIso U₂.rightDerivedFunctorPlusUnit) =
      derivedVPaste P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ₁ τ₂ :=
  Functor.rightDerived_ext (P.rightDerivedFunctorPlus ⋙ U₂.rightDerivedFunctorPlus)
    (compUnit P U₂) (HomotopyCategory.Plus.quasiIso A₀) _ _ _
    (NatTrans.ext (funext fun K ↦
      unit_comp_derived_eq_derivedVPaste_app P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ τ₁ τ₂ hτ K))

/-- **The vertical pasting law for the derived base change comparison, evaluated at an
object.** -/
theorem derived_eq_derivedVPaste_app
    (hτ : ∀ X, τ.app X = U₂.map (cP.inv.app X) ≫ τ₂.app (P₁.obj X) ≫
      P₂'.map (τ₁.app X) ≫ cP'.hom.app (U₀.obj X))
    (M : DerivedCategory.Plus A₀) :
    (derived P P' U₂ U₀ τ (asIso U₂.rightDerivedFunctorPlusUnit)).app M =
      U₂.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
            P₁ P₂ P cP).inv.app M) ≫
        (derived P₂ P₂' U₂ U₁ τ₂ (asIso U₂.rightDerivedFunctorPlusUnit)).app
            (P₁.rightDerivedFunctorPlus.obj M) ≫
          P₂'.rightDerivedFunctorPlus.map
              ((derived P₁ P₁' U₁ U₀ τ₁ (asIso U₁.rightDerivedFunctorPlusUnit)).app M) ≫
            (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
                P₁' P₂' P' cP').hom.app
              (U₀.rightDerivedFunctorPlus.obj M) := by
  rw [derived_eq_derivedVPaste P₁ P₂ P P₁' P₂' P' U₀ U₁ U₂ cP cP' τ τ₁ τ₂ hτ,
    derivedVPaste_app]

end VPaste

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.BaseChange

/-! ### The named-composite derived direct image comparison -/

section DerivedPushforwardComp

variable {X Y Z : Scheme.{u}}

/-- **The composition isomorphism `Ra_* ⋙ Rb_* ≅ R(ab)_*`** for direct image of abelian sheaves
on the small étale sites, on the bounded below derived categories, with the composite carried as
a named morphism.

This is `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso` with the composite named;
no hypothesis on `a` or `b` is needed, direct image preserving injective objects for every
morphism of schemes. -/
public def smallEtaleDerivedPushforwardAbCompIso' (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
    (hab : ab = a ≫ b) :
    (smallEtalePushforwardAb a).rightDerivedFunctorPlus ⋙
        (smallEtalePushforwardAb b).rightDerivedFunctorPlus ≅
      (smallEtalePushforwardAb ab).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives (smallEtalePushforwardAb a)
    (smallEtalePushforwardAb b) (smallEtalePushforwardAb ab)
    (smallEtalePushforwardAbCompIso' a b ab hab)

end DerivedPushforwardComp

/-! ### The étale vertical pasting law -/

section Paste

variable {S T X' Y T' Y' : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T')

/-- **The pasting law for the derived base change comparison of abelian small étale sheaves,
along the direct image legs.** For two commutative squares of schemes sharing a vertical edge,
the derived base change comparison of the outer rectangle is the composite of the derived
comparisons of the two squares, read through the comparisons of the derived direct images along
the two composite horizontal legs `G = π ≫ g` and `H = π' ≫ h`.

The hypotheses are the commutativity of the two squares and nothing else: no cartesianness, no
finiteness and no torsion assumption enters. This is the bounded-below derived form of
[Stacks, Tag 0E46] for the small étale sites of schemes with abelian coefficients; the underived
form is `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_pasteDirectImage_app`, which is the only
input beyond the generic `Stacks.Cohomology.BaseChange.derived_eq_derivedVPaste`. -/
public theorem smallEtaleDerivedBaseChangeAb_eq_derivedVPaste
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (wo : H ≫ f' = e' ≫ G) :
    smallEtaleDerivedBaseChangeAb f' G H e' wo =
      derivedVPaste (smallEtalePushforwardAb π) (smallEtalePushforwardAb g)
        (smallEtalePushforwardAb G) (smallEtalePushforwardAb π')
        (smallEtalePushforwardAb h) (smallEtalePushforwardAb H)
        (smallEtalePullbackAb e') (smallEtalePullbackAb e) (smallEtalePullbackAb f')
        (smallEtalePushforwardAbCompIso' π g G hG)
        (smallEtalePushforwardAbCompIso' π' h H hH)
        (smallEtaleBaseChangeAb e π π' e' w') (smallEtaleBaseChangeAb f' g h e w) :=
  derived_eq_derivedVPaste (smallEtalePushforwardAb π) (smallEtalePushforwardAb g)
    (smallEtalePushforwardAb G) (smallEtalePushforwardAb π')
    (smallEtalePushforwardAb h) (smallEtalePushforwardAb H)
    (smallEtalePullbackAb e') (smallEtalePullbackAb e) (smallEtalePullbackAb f')
    (smallEtalePushforwardAbCompIso' π g G hG)
    (smallEtalePushforwardAbCompIso' π' h H hH)
    (smallEtaleBaseChangeAb f' G H e' wo)
    (smallEtaleBaseChangeAb e π π' e' w') (smallEtaleBaseChangeAb f' g h e w)
    (smallEtaleBaseChangeAb_pasteDirectImage_app f' g h e π π' e' w w' G hG H hH wo)

/-- **The derived pasting law along the direct image legs, evaluated at a bounded below
complex.** -/
public theorem smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (wo : H ≫ f' = e' ≫ G)
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology T') Ab.{u + 1})) :
    (smallEtaleDerivedBaseChangeAb f' G H e' wo).app M =
      (smallEtalePullbackAb f').rightDerivedFunctorPlus.map
          ((smallEtaleDerivedPushforwardAbCompIso' π g G hG).inv.app M) ≫
        (smallEtaleDerivedBaseChangeAb f' g h e w).app
            ((smallEtalePushforwardAb π).rightDerivedFunctorPlus.obj M) ≫
          (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
              ((smallEtaleDerivedBaseChangeAb e π π' e' w').app M) ≫
            (smallEtaleDerivedPushforwardAbCompIso' π' h H hH).hom.app
              ((smallEtalePullbackAb e').rightDerivedFunctorPlus.obj M) :=
  derived_eq_derivedVPaste_app (smallEtalePushforwardAb π) (smallEtalePushforwardAb g)
    (smallEtalePushforwardAb G) (smallEtalePushforwardAb π')
    (smallEtalePushforwardAb h) (smallEtalePushforwardAb H)
    (smallEtalePullbackAb e') (smallEtalePullbackAb e) (smallEtalePullbackAb f')
    (smallEtalePushforwardAbCompIso' π g G hG)
    (smallEtalePushforwardAbCompIso' π' h H hH)
    (smallEtaleBaseChangeAb f' G H e' wo)
    (smallEtaleBaseChangeAb e π π' e' w') (smallEtaleBaseChangeAb f' g h e w)
    (smallEtaleBaseChangeAb_pasteDirectImage_app f' g h e π π' e' w w' G hG H hH wo) M

/-- **Two out of three for the derived pasting law along the direct image legs.** If the derived
comparison of the outer rectangle and the derived comparison of the upper square are invertible
at the relevant objects, so is the derived comparison of the lower square: the remaining factors
in `smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app` are components of isomorphisms.

This is the shape the integral-base steps of [Stacks, Tag 0F02] consume: there the upper square
is a base change of an integral morphism, and its comparison is invertible by
[Stacks, Tag 0EYP]. -/
public theorem isIso_smallEtaleDerivedBaseChangeAb_of_isIso_derivedVPaste
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (wo : H ≫ f' = e' ≫ G)
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology T') Ab.{u + 1}))
    (houter : IsIso ((smallEtaleDerivedBaseChangeAb f' G H e' wo).app M))
    (hupper : IsIso ((smallEtaleDerivedBaseChangeAb e π π' e' w').app M)) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((smallEtalePushforwardAb π).rightDerivedFunctorPlus.obj M)) := by
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app f' g h e π π' e' w w' G hG H hH wo M,
    isIso_comp_left_iff, isIso_comp_right_iff] at houter
  exact houter

end Paste

end Stacks.EtaleCohomology

end
