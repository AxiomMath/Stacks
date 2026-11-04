module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.LongExactSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images onto a chaotic site are cohomology over objects

Let `u : 𝒟 ⥤ 𝒞` be a functor of sites, continuous for the **chaotic** topology `⊥` on `𝒟` and a
topology `K` on `𝒞`, and let `f_* = u^s` be the direct image of abelian sheaves along it, so that
`f_* F = F|_𝒟`.  Because every presheaf on `𝒟` is a sheaf for the chaotic topology, the forgetful
functor `Sheaf ⊥ 𝒜 ⥤ 𝒟ᵒᵖ ⥤ 𝒜` is an equivalence, hence exact, and therefore the sections functor
`Γ(V, -)` on `Sh(⊥)` is exact for every object `V` of `𝒟`.  Pulling that exact functor out of a
right derived functor gives

`Γ(V, R^p f_* F) ≅ R^p Γ(u V, F)`,

the sections of the `p`-th higher direct image over an object `V` of `𝒟` being the `p`-th right
derived sections of `F` over the image object `u V` of `𝒞`.  This is
[Stacks, Tag 072W] — the higher direct image is the sheafification of `V ↦ H^p(u V, F)` — in the
case where no sheafification is needed, the target topology being chaotic.

As a consequence the higher direct images **vanish** exactly when the right derived sections over
the objects in the image of `u` vanish, which is the form in which the Leray argument of
[Stacks, Tag 07JK] consumes the vanishing theorem [Stacks, Tag 07JJ].

## Main results

All in the namespace `Stacks.Cohomology.ChaoticSite`.

* `isEquivalence_sheafToPresheaf_bot` — sheaves for the chaotic topology are presheaves.
* `higherDirectImageSectionsIso` — **`Γ(V, R^p f_* -) ≅ R^p Γ(u V, -)`**, naturally in the sheaf.
* `isZero_of_forall_isZero_sections` — a sheaf on a chaotic site is zero as soon as all its
  groups of sections are.
* `isZero_higherDirectImage_of_isZero_rightDerivedSections` — **the `p`-th higher direct image of
  `F` onto a chaotic site vanishes as soon as the `p`-th right derived sections of `F` over every
  object in the image of `u` vanish.**

## What is and is not proved

What is proved is the chaotic case of [Stacks, Tag 072W]: the identification of the sections of a
higher direct image over an object with right derived sections over the image object, and the
vanishing criterion it yields.  No tag attribute is placed: [Stacks, Tag 072W] asserts the
identification of `R^p f_*` with the *sheafification* of the cohomology presheaf for an arbitrary
morphism of topoi coming from a continuous functor, and only the case of a chaotic target, where
the sheafification is the identity, is proved here.

Nothing here requires the direct image to be exact or to preserve injective objects, and neither
is available for a restriction to a chaotic site: the exact functor pulled out of the right
derived functor is the *sections* functor on the chaotic site, which is postcomposed, not the
direct image, which is precomposed.  That asymmetry is the whole content of the file.  Indeed a
restriction to a chaotic subsite can *not* both be right exact and preserve injectives, since
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardRightDerivedSheafToPresheafIso` would
then force `H^p(u V, F) = 0` for every abelian sheaf `F`, every `V` and every `p > 0`.

## Implementation notes

The equivalence `CategoryTheory.sheafBotEquivalence` has `sheafToPresheaf` as its functor on the
nose, so the exactness of the sections functor on a chaotic site is the exactness of an
equivalence followed by an evaluation, and `CategoryTheory.Functor.preservesHomologyOfExact`
turns that into the hypothesis that
`CategoryTheory.Functor.rightDerivedCompIso` needs.

The identification `u^s ⋙ Γ(V, -) = Γ(u V, -)` is
`Stacks.Cohomology.BiggerSiteGlobal.sheafSections_comp_sheafPushforwardContinuous`, an equality of
functors by `rfl`, so the isomorphism below is literally `rightDerivedCompIso` with its left-hand
side read through that equality; no transport appears in the term.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace Stacks.Cohomology.ChaoticSite

universe vA uA v₁ u₁ v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] {C : Type u₁} [Category.{v₁} C]
  (K : GrothendieckTopology C) (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasSheafify (⊥ : GrothendieckTopology D) A] [HasSheafify K A]

/-- **Sheaves for the chaotic topology are presheaves**: the forgetful functor
`Sheaf ⊥ 𝒜 ⥤ 𝒟ᵒᵖ ⥤ 𝒜` is an equivalence, being the functor of
`CategoryTheory.sheafBotEquivalence`.  This is the second assertion of [Stacks, Tag 07GE], read
as a property of `sheafToPresheaf` rather than as an equivalence of categories, which is the
form instance search can use. -/
@[sga "4 IV 6.8.6" "more general"]
instance isEquivalence_sheafToPresheaf_bot :
    (sheafToPresheaf (⊥ : GrothendieckTopology D) A).IsEquivalence :=
  inferInstanceAs ((sheafBotEquivalence A).functor.IsEquivalence)

/-- Sections over an object of a chaotic site are left exact, being an equivalence followed by an
evaluation. -/
instance preservesFiniteLimits_sheafSections_bot (V : D) :
    PreservesFiniteLimits ((sheafSections (⊥ : GrothendieckTopology D) A).obj (op V)) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf (⊥ : GrothendieckTopology D) A ⋙ (evaluation Dᵒᵖ A).obj (op V)))

/-- **Sections over an object of a chaotic site are right exact.**  This is what fails for a
site with a nontrivial topology, where a cokernel of sheaves is the sheafification of the
presheaf cokernel. -/
instance preservesFiniteColimits_sheafSections_bot (V : D) :
    PreservesFiniteColimits ((sheafSections (⊥ : GrothendieckTopology D) A).obj (op V)) :=
  inferInstanceAs (PreservesFiniteColimits
    (sheafToPresheaf (⊥ : GrothendieckTopology D) A ⋙ (evaluation Dᵒᵖ A).obj (op V)))

/-- Sections over an object of a chaotic site preserve homology, being exact. -/
instance preservesHomology_sheafSections_bot (V : D) :
    ((sheafSections (⊥ : GrothendieckTopology D) A).obj (op V)).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- Sections of abelian sheaves over an object are additive, being the forgetful functor to
presheaves followed by an evaluation. -/
instance additive_sheafSections_obj (X : C) :
    ((sheafSections K A).obj (op X)).Additive :=
  inferInstanceAs ((sheafToPresheaf K A ⋙ (evaluation Cᵒᵖ A).obj (op X)).Additive)

variable (u : D ⥤ C) [u.IsContinuous (⊥ : GrothendieckTopology D) K]
  [EnoughInjectives (Sheaf K A)]

/-- **The sections of a higher direct image onto a chaotic site over an object are the right
derived sections over the image object**: for every degree `p` and every object `V` of `𝒟`,

`Γ(V, R^p f_* F) ≅ R^p Γ(u V, F)`,

naturally in the abelian sheaf `F` on `(𝒞, K)`.

This is the chaotic case of [Stacks, Tag 072W].  Sections over `V` on the chaotic site are an
exact functor, so they come out of the right derived functor
(`CategoryTheory.Functor.rightDerivedCompIso`), and the composite of the direct image with them
*is* the sections functor over `u V`. -/
def higherDirectImageSectionsIso (p : ℕ) (V : D) :
    HigherDirectImageDelta.higherDirectImage (⊥ : GrothendieckTopology D) K A u p ⋙
        (sheafSections (⊥ : GrothendieckTopology D) A).obj (op V) ≅
      ((sheafSections K A).obj (op (u.obj V))).rightDerived p :=
  (Functor.rightDerivedCompIso (u.sheafPushforwardContinuous A (⊥ : GrothendieckTopology D) K)
    ((sheafSections (⊥ : GrothendieckTopology D) A).obj (op V)) p).symm

omit [HasSheafify (⊥ : GrothendieckTopology D) A] in
/-- **A sheaf on a chaotic site is zero as soon as all its groups of sections are.**  A morphism
of sheaves is a morphism of the underlying presheaves, so the identity of the sheaf is zero as
soon as it is zero on every object. -/
theorem isZero_of_forall_isZero_sections {G : Sheaf (⊥ : GrothendieckTopology D) A}
    (h : ∀ V : D, IsZero (G.obj.obj (op V))) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  exact Sheaf.hom_ext <| NatTrans.ext <| funext fun V => (h V.unop).eq_of_src _ _

/-- **The higher direct images onto a chaotic site vanish as soon as the right derived sections
over the objects in the image vanish.**  For an abelian sheaf `F` on `(𝒞, K)` and a degree `p`,
if `R^p Γ(u V, F) = 0` for every object `V` of `𝒟`, then `R^p f_* F = 0`.

This is the form in which the Leray argument of [Stacks, Tag 07JK] consumes the vanishing
theorem [Stacks, Tag 07JJ]: the hypothesis is a statement about cohomology over objects of `𝒞`,
which is what 07JJ provides, and the conclusion is the vanishing of the higher direct images,
which is what the degeneration of the Leray spectral sequence needs. -/
theorem isZero_higherDirectImage_of_isZero_rightDerivedSections (F : Sheaf K A) (p : ℕ)
    (h : ∀ V : D, IsZero ((((sheafSections K A).obj (op (u.obj V))).rightDerived p).obj F)) :
    IsZero ((HigherDirectImageDelta.higherDirectImage
      (⊥ : GrothendieckTopology D) K A u p).obj F) :=
  isZero_of_forall_isZero_sections (A := A) fun V =>
    (h V).of_iso ((higherDirectImageSectionsIso K A u p V).app F)

end Stacks.Cohomology.ChaoticSite

end

end
