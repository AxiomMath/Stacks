module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.UniversalOver

/-!
# The projective bundle represents the invertible quotients of the pulled-back module

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `π : 𝐏(F) ⟶ X` its projective bundle.
For a scheme `f : T ⟶ X` over `X`, the morphisms `h : T ⟶ 𝐏(F)` with `h ≫ π = f` correspond to
the invertible quotients `f^*F ↠ 𝓛` up to isomorphism, the morphism `h` going to the quotient
`f^*F ≅ h^*π^*F ⟶ h^*𝒪(1)` pulled back from the tautological one, and this correspondence is
natural in `T`. This is the description of `𝐏(F)` that the discussion of [Stacks, Section 27.21]
deduces from [Stacks, Tag 01O4], the graded algebra maps `Sym(f^*F) ⟶ ⨁ₙ 𝓛^{⊗ n}` being the
module maps `f^*F ⟶ 𝓛`.

Here it is assembled from two unconditional bijections, and nothing is assumed:

* `Stacks.RelativeProj.overMorphismEquivSection`: as the square of
  `Stacks.RelativeProj.isPullback_projectiveBundleBaseChange` is cartesian, the morphisms
  `T ⟶ 𝐏(F)` over `f` are the sections of `𝐏(F') ⟶ T` for any quasi-coherent `F' ≅ f^*F`;
* `Stacks.RelativeProj.projectiveBundleSectionsEquiv`: [Stacks, Tag 0B3V]'s bijection between the
  sections of `𝐏(F') ⟶ T` and the invertible quotients of `F'`.

What is new is the **normalisation**: the composite bijection sends `h` to the class of the
quotient that `h` pulls back from the tautological quotient on `𝐏(F)` *directly*
(`Stacks.RelativeProj.projectiveBundleOverEquiv_apply`), rather than through the base-changed
bundle `𝐏(F')`, which is how `StacksFrontier.AlgebraicGeometry.ProjectiveBundle.UniversalOver` left
it. The comparison is the pseudofunctoriality of pullback together with the identification of
the tautological quotient of `𝐏(F')` with the pullback of that of `𝐏(F)`,
`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec'`. **Naturality** in the test
scheme (`Stacks.RelativeProj.projectiveBundleOverEquiv_comp`) then follows from the
normalisation by pseudofunctoriality alone.

The same statements are then read on the other presentation of the bundle, the relative `Proj`
of the graded algebra `Stacks.SymGraded.schemeSheafGradedAlgebra F` with its twist
`Stacks.ProjectiveBundleSplitting.tautologicalTwist` and tautological map
`Stacks.ProjectiveBundleSplitting.tautologicalMap` (`Stacks.RelativeProj.symGradedOverEquiv`),
through the comparison `Stacks.RelativeProj.bundlePresentationIso`. That presentation is the one
`Stacks.Chow.bundle` is built on.

## Main definitions

* `Stacks.Modules.quotientMapAlong`: for `p : P ⟶ X` and a map `u : p^*F ⟶ 𝓛`, the map
  `(h ≫ p)^*F ⟶ h^*𝓛` that `u` induces along `h : T ⟶ P`.
* `Stacks.RelativeProj.projectiveBundleOverEquiv`: **the bijection** between the morphisms
  `T ⟶ 𝐏(F)` over `f` and the classes of invertible quotients of `F' ≅ f^*F`.
* `Stacks.RelativeProj.symGradedOverEquiv`: the same bijection on the `SheafGradedAlgebra`
  presentation of the bundle.

## Main results

* `Stacks.Modules.quotientMapAlong_comp`: the induced map along a composite.
* `Stacks.RelativeProj.projectiveBundleOverEquiv_apply`: **the bijection is normalised by the
  tautological quotient**: `h` goes to the class of
  `Stacks.RelativeProj.TautologicalDatum.overQuotient` of the tautological datum.
* `Stacks.RelativeProj.projectiveBundleOverEquiv_eq_iff`: `h` goes to the class of `Q` exactly
  when `h^*𝒪(1) ≅ Q.L` compatibly with the quotient maps.
* `Stacks.RelativeProj.projectiveBundleOverEquiv_comp`: **naturality in the test scheme**: the
  bijection at `k ≫ f` sends `k ≫ h` to the base change along `k` of the class of `h`.
* `Stacks.RelativeProj.symGradedOverEquiv_apply`, `Stacks.RelativeProj.symGradedOverEquiv_eq_iff`,
  `Stacks.RelativeProj.symGradedOverEquiv_comp`: the same on the `SheafGradedAlgebra`
  presentation.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Modules

section Coherence

variable {A B C D : Scheme.{u}}

/-- **Associativity of the comparison of iterated pullbacks**, in the inverse direction and with
the outer composite split off: `((k ≫ h) ≫ p)^* ≅ (k ≫ h)^* p^*` is `k^*` of
`(h ≫ p)^* ≅ h^* p^*`, transported along `k^* h^* ≅ (k ≫ h)^*`. This is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` read at one module. -/
@[reassoc]
theorem pullbackComp_comp_inv_app (k : A ⟶ B) (h : B ⟶ C) (p : C ⟶ D) (M : D.Modules) :
    (Scheme.Modules.pullbackComp (k ≫ h) p).inv.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc k h p)).hom.app M ≫
        (Scheme.Modules.pullbackComp k (h ≫ p)).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp h p).inv.app M) ≫
        (Scheme.Modules.pullbackComp k h).hom.app ((Scheme.Modules.pullback p).obj M) := by
  have hassoc := congrArg (fun η => NatTrans.app η M)
    (Scheme.Modules.pseudofunctor_associativity k h p)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at hassoc
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (k ≫ h) p).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hassoc]
  simp [Scheme.Modules.pullbackCongr]

/-- **Right unitality of the comparison of iterated pullbacks**, in the inverse direction:
`(𝟙 ≫ p)^* ≅ 𝟙^* p^*` is the identification `p^* ≅ 𝟙^* p^*`. -/
@[reassoc]
theorem pullbackComp_id_left_inv_app (p : A ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 A) p).inv.app M =
      (Scheme.Modules.pullbackCongr (Category.id_comp p)).hom.app M ≫
        (Scheme.Modules.pullbackId A).inv.app ((Scheme.Modules.pullback p).obj M) := by
  have hu := congrArg (fun η => NatTrans.app η M)
    (Scheme.Modules.pseudofunctor_right_unitality p)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at hu
  rw [← cancel_mono ((Scheme.Modules.pullbackId A).hom.app ((Scheme.Modules.pullback p).obj M)),
    Category.assoc, Iso.inv_hom_id_app]
  simpa [Scheme.Modules.pullbackCongr] using hu

/-- **Right unitality of the comparison of iterated pullbacks**, in the forward direction. -/
@[reassoc]
theorem pullbackComp_id_left_hom_app (p : A ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 A) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.id_comp p)).hom.app M =
      (Scheme.Modules.pullbackId A).hom.app ((Scheme.Modules.pullback p).obj M) := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 A) p).inv.app M), Iso.inv_hom_id_app_assoc,
    pullbackComp_id_left_inv_app_assoc, Iso.inv_hom_id_app]
  simp [Scheme.Modules.pullbackCongr]

/-- **Transport of the comparison of iterated pullbacks along an equality of the inner
morphism.** -/
@[reassoc]
theorem pullbackComp_inv_app_congr_right (k : A ⟶ B) {c c' : B ⟶ C} (e : c = c')
    (M : C.Modules) :
    (Scheme.Modules.pullbackComp k c).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackCongr e).hom.app M) =
      (Scheme.Modules.pullbackCongr (congrArg (fun t => k ≫ t) e)).hom.app M ≫
        (Scheme.Modules.pullbackComp k c').inv.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

variable {T X P P' : Scheme.{u}}

/-- **The coherence behind the normalisation of the bijection, forward direction**: for a section
`σ` of `p' : P' ⟶ T` and a morphism `b : P' ⟶ P` over `f : T ⟶ X` with `σ ≫ b = h`, the two
identifications of `h^*p^*M` with `f^*M` — directly, and through `σ^*b^*p^*M ≅ σ^*p'^*f^*M` and
the section — agree. No scheme here is a projective bundle: this is the pseudofunctoriality of
pullback, `Stacks.Modules.pullbackComp_congr_assoc` twice and right unitality once. -/
theorem section_comp_coherence_hom (f : T ⟶ X) (p : P ⟶ X) (p' : P' ⟶ T) (b : P' ⟶ P)
    (hb : b ≫ p = p' ≫ f) (σ : T ⟶ P') (hσ : σ ≫ p' = 𝟙 T) (h : T ⟶ P) (hσb : σ ≫ b = h)
    (hh : h ≫ p = f) (M : X.Modules) :
    (Scheme.Modules.pullbackComp h p).hom.app M ≫ (Scheme.Modules.pullbackCongr hh).hom.app M =
      (Scheme.Modules.pullbackCongr hσb).inv.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackComp σ b).inv.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp b p).hom.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackCongr hb).hom.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp p' f).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ p').hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackId T).hom.app ((Scheme.Modules.pullback f).obj M) := by
  have A1 := pullbackComp_congr_assoc σ b p h hσb (p' ≫ f) hb f hh M
  have A2 := pullbackComp_congr_assoc σ p' f (𝟙 T) hσ (p' ≫ f) rfl f (Category.id_comp f) M
  have hrfl : (Scheme.Modules.pullbackCongr (rfl : p' ≫ f = p' ≫ f)).hom.app M = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  rw [hrfl, Category.comp_id, Category.assoc, pullbackComp_id_left_hom_app] at A2
  simp only [Functor.map_comp, Category.assoc] at A1 A2
  have c : ∀ {Z : T.Modules} (k : (Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback (p' ≫ f)).obj M) ⟶ Z),
      (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp p' f).inv.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp p' f).hom.app M) ≫ k =
          k := by
    intro Z k
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← A2, c, A1]
  simp

/-- **The coherence behind the normalisation of the bijection**, in the inverse direction in
which quotient maps pulled back along a section are written: the identification of `f^*M` with
`σ^*p'^*f^*M` given by the section, followed by the base-change comparison
`σ^*p'^*f^*M ≅ σ^*b^*p^*M ≅ h^*p^*M`, is the direct identification of `f^*M` with `h^*p^*M`. -/
@[reassoc]
theorem section_comp_coherence (f : T ⟶ X) (p : P ⟶ X) (p' : P' ⟶ T) (b : P' ⟶ P)
    (hb : b ≫ p = p' ≫ f) (σ : T ⟶ P') (hσ : σ ≫ p' = 𝟙 T) (h : T ⟶ P) (hσb : σ ≫ b = h)
    (hh : h ≫ p = f) (M : X.Modules) :
    (Scheme.Modules.pullbackId T).inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ).inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp σ p').inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp p' f).hom.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackCongr hb).inv.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp b p).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ b).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackCongr hσb).hom.app ((Scheme.Modules.pullback p).obj M) =
      (Scheme.Modules.pullbackCongr hh).inv.app M ≫
        (Scheme.Modules.pullbackComp h p).inv.app M := by
  have H := section_comp_coherence_hom f p p' b hb σ hσ h hσb hh M
  have e := congrArg Iso.inv (Iso.ext (α := (Scheme.Modules.pullbackComp h p).app M ≪≫
      (Scheme.Modules.pullbackCongr hh).app M)
    (β := ((Scheme.Modules.pullbackCongr hσb).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp σ b).app _).symm ≪≫
      (Scheme.Modules.pullback σ).mapIso ((Scheme.Modules.pullbackComp b p).app M) ≪≫
      (Scheme.Modules.pullback σ).mapIso ((Scheme.Modules.pullbackCongr hb).app M) ≪≫
      (Scheme.Modules.pullback σ).mapIso ((Scheme.Modules.pullbackComp p' f).app M).symm ≪≫
      (Scheme.Modules.pullbackComp σ p').app _ ≪≫ (Scheme.Modules.pullbackCongr hσ).app _ ≪≫
      (Scheme.Modules.pullbackId T).app _) (by simpa using H))
  simpa using e.symm

/-- **The comparison of quotient maps behind the normalisation of the bijection.** Let
`b : P' ⟶ P` lie over `f : T ⟶ X` (`b ≫ p = p' ≫ f`), let `u : p^*F ⟶ 𝓛` and `u' : p'^*F' ⟶ 𝓛'`
be maps out of pullbacks with `F' ≅ f^*F`, identified by `β : b^*𝓛 ≅ 𝓛'` (`hβ`), and let `σ` be a
section of `p'` with `σ ≫ b = h`. Then the quotient map of `F'` that `σ` pulls back from `u'`,
followed by `σ^*β⁻¹` and `σ^*b^* ≅ h^*`, is the quotient map of `F'` that `h` pulls back from `u`.
No scheme here is a projective bundle. -/
theorem section_quotient_comparison {F : X.Modules} (F' : T.Modules)
    {f : T ⟶ X} (hF : F' ≅ (Scheme.Modules.pullback f).obj F) (p : P ⟶ X) (p' : P' ⟶ T)
    (b : P' ⟶ P) (hb : b ≫ p = p' ≫ f) {L : P.Modules} {L' : P'.Modules}
    (u : (Scheme.Modules.pullback p).obj F ⟶ L) (u' : (Scheme.Modules.pullback p').obj F' ⟶ L')
    (β : (Scheme.Modules.pullback b).obj L ≅ L')
    (hβ : (Scheme.Modules.pullback b).map u ≫ β.hom =
      (Scheme.Modules.pullbackComp b p).hom.app F ≫ (Scheme.Modules.pullbackCongr hb).hom.app F ≫
        (Scheme.Modules.pullbackComp p' f).inv.app F ≫
        (Scheme.Modules.pullback p').map hF.inv ≫ u')
    (σ : T ⟶ P') (hσ : σ ≫ p' = 𝟙 T) (h : T ⟶ P) (hσb : σ ≫ b = h) (hh : h ≫ p = f) :
    ((Scheme.Modules.pullbackId T).inv.app F' ≫ (Scheme.Modules.pullbackCongr hσ).inv.app F' ≫
        (Scheme.Modules.pullbackComp σ p').inv.app F' ≫ (Scheme.Modules.pullback σ).map u') ≫
      ((Scheme.Modules.pullback σ).mapIso β.symm ≪≫ (Scheme.Modules.pullbackComp σ b).app L ≪≫
        (Scheme.Modules.pullbackCongr hσb).app L).hom =
      hF.hom ≫ (Scheme.Modules.pullbackCongr hh).inv.app F ≫
        (Scheme.Modules.pullbackComp h p).inv.app F ≫ (Scheme.Modules.pullback h).map u := by
  have hβ' : u' ≫ β.inv = (Scheme.Modules.pullback p').map hF.hom ≫
      (Scheme.Modules.pullbackComp p' f).hom.app F ≫ (Scheme.Modules.pullbackCongr hb).inv.app F ≫
      (Scheme.Modules.pullbackComp b p).inv.app F ≫ (Scheme.Modules.pullback b).map u := by
    rw [Iso.comp_inv_eq]
    simp [hβ]
  have n1 := (Scheme.Modules.pullbackComp σ b).hom.naturality u
  have n2 := (Scheme.Modules.pullbackCongr hσb).hom.naturality u
  have m1 := (Scheme.Modules.pullbackComp σ p').inv.naturality hF.hom
  have m2 := (Scheme.Modules.pullbackCongr hσ).inv.naturality hF.hom
  have m3 := (Scheme.Modules.pullbackId T).inv.naturality hF.hom
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n1 n2 m1 m2 m3
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback σ) u' β.inv, hβ']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, n2, ← reassoc_of% m1, ← reassoc_of% m2, ← reassoc_of% m3,
    section_comp_coherence_assoc f p p' b hb σ hσ h hσb hh F]

end Coherence

section QuotientMapAlong

variable {T' T P X : Scheme.{u}} {F : X.Modules} (p : P ⟶ X) {L : P.Modules}
  (u : (Scheme.Modules.pullback p).obj F ⟶ L)

/-- **The map induced along a morphism into `P` by a map out of a pullback to `P`**: for
`p : P ⟶ X`, `u : p^*F ⟶ 𝓛` and `h : T ⟶ P`, the map `(h ≫ p)^*F ≅ h^*p^*F ⟶ h^*𝓛`. When
`u` is the tautological quotient of a projective bundle this is the quotient that `h` pulls back
from it. -/
def quotientMapAlong (h : T ⟶ P) :
    (Scheme.Modules.pullback (h ≫ p)).obj F ⟶ (Scheme.Modules.pullback h).obj L :=
  (Scheme.Modules.pullbackComp h p).inv.app F ≫ (Scheme.Modules.pullback h).map u

/-- The induced map along a morphism is surjective when the map it is induced by is. -/
instance epi_quotientMapAlong [Epi u] (h : T ⟶ P) : Epi (quotientMapAlong p u h) := by
  unfold quotientMapAlong
  infer_instance

/-- **The induced map along a composite** is the pullback of the induced map, read through the
comparisons of iterated pullbacks. -/
theorem quotientMapAlong_comp (k : T' ⟶ T) (h : T ⟶ P) :
    quotientMapAlong p u (k ≫ h) =
      (Scheme.Modules.pullbackCongr (Category.assoc k h p)).hom.app F ≫
        (Scheme.Modules.pullbackComp k (h ≫ p)).inv.app F ≫
        (Scheme.Modules.pullback k).map (quotientMapAlong p u h) ≫
        (Scheme.Modules.pullbackComp k h).hom.app L := by
  have hnat := (Scheme.Modules.pullbackComp k h).hom.naturality u
  dsimp only [Functor.comp_map] at hnat
  simp only [quotientMapAlong, pullbackComp_comp_inv_app, Functor.map_comp, Category.assoc, hnat]

/-- The induced map is transported along an equality of morphisms into `P`. -/
@[reassoc]
theorem quotientMapAlong_congr {h h' : T ⟶ P} (e : h = h') :
    quotientMapAlong p u h ≫ (Scheme.Modules.pullbackCongr e).hom.app L =
      (Scheme.Modules.pullbackCongr (congrArg (fun t => t ≫ p) e)).hom.app F ≫
        quotientMapAlong p u h' := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/-- The induced map along the identity is the given map, read through the unit comparisons. -/
theorem quotientMapAlong_id :
    quotientMapAlong p u (𝟙 P) ≫ (Scheme.Modules.pullbackId P).hom.app L =
      (Scheme.Modules.pullbackCongr (Category.id_comp p)).hom.app F ≫ u := by
  have hnat := (Scheme.Modules.pullbackId P).hom.naturality u
  dsimp only [Functor.id_map] at hnat
  simp only [quotientMapAlong, pullbackComp_id_left_inv_app, Category.assoc, hnat,
    Iso.inv_hom_id_app_assoc]

/-- The induced map, as the composite it is defined to be. -/
theorem quotientMapAlong_eq (h : T ⟶ P) :
    quotientMapAlong p u h =
      (Scheme.Modules.pullbackComp h p).inv.app F ≫ (Scheme.Modules.pullback h).map u :=
  rfl

/-- **The quotient map induced along a composite is the base change of the one induced along the
second factor.** For `h : T ⟶ P` over `f` and `k : T' ⟶ T`, with `F' ≅ f^*F` and `F'' ≅ k^*F'`,
the quotient map of `F''` that `k ≫ h` induces from `u`, followed by `(k ≫ h)^* ≅ k^*h^*`, is
`k^*` of the quotient map of `F'` that `h` induces, read out of `F''`. -/
theorem quotientMapAlong_comp_baseChange {f : T ⟶ X} (F' : T.Modules)
    (hF : F' ≅ (Scheme.Modules.pullback f).obj F) (k : T' ⟶ T) (F'' : T'.Modules)
    (hF'' : F'' ≅ (Scheme.Modules.pullback k).obj F') (h : T ⟶ P) (hh : h ≫ p = f)
    (hkh : (k ≫ h) ≫ p = k ≫ f) :
    ((hF'' ≪≫ (Scheme.Modules.pullback k).mapIso hF ≪≫
        (Scheme.Modules.pullbackComp k f).app F).hom ≫
      (Scheme.Modules.pullbackCongr hkh).inv.app F ≫ quotientMapAlong p u (k ≫ h)) ≫
      ((Scheme.Modules.pullbackComp k h).app L).symm.hom =
    hF''.hom ≫ (Scheme.Modules.pullback k).map
      (hF.hom ≫ (Scheme.Modules.pullbackCongr hh).inv.app F ≫ quotientMapAlong p u h) := by
  have e := pullbackComp_inv_app_congr_right k hh.symm F
  rw [pullbackCongr_symm_hom hh] at e
  have e' : (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackCongr hh).inv.app F) =
      (Scheme.Modules.pullbackComp k f).hom.app F ≫
        (Scheme.Modules.pullbackCongr (congrArg (fun t => k ≫ t) hh.symm)).hom.app F ≫
        (Scheme.Modules.pullbackComp k (h ≫ p)).inv.app F := by
    rw [← e, Iso.hom_inv_id_app_assoc]
  rw [quotientMapAlong_comp]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app, e']
  simp [Scheme.Modules.pullbackCongr]

/-- **The quotient map induced along a morphism through a comparison of presentations.** Let
`j : P ⟶ P₀` lie over `X` (`j ≫ p₀ = p`) and let the map `p^*F ⟶ j^*𝓛₀` be the one induced by
`u₀ : p₀^*F ⟶ 𝓛₀` along `j`. Then for `a : T ⟶ P` over `f`, the quotient map of `F'` that `a`
induces from it, followed by `a^*j^* ≅ (a ≫ j)^* = g^*`, is the quotient map of `F'` that `g`
induces from `u₀`. -/
theorem quotientMapAlong_presentation {P₀ : Scheme.{u}} {f : T ⟶ X} (F' : T.Modules)
    (hF : F' ≅ (Scheme.Modules.pullback f).obj F) (p₀ : P₀ ⟶ X) {L₀ : P₀.Modules}
    (u₀ : (Scheme.Modules.pullback p₀).obj F ⟶ L₀) (j : P ⟶ P₀) (hj : j ≫ p₀ = p)
    (a : T ⟶ P) (ha : a ≫ p = f) (g : T ⟶ P₀) (e : a ≫ j = g) (hg : g ≫ p₀ = f) :
    (hF.hom ≫ (Scheme.Modules.pullbackCongr ha).inv.app F ≫
        quotientMapAlong p ((Scheme.Modules.pullbackCongr hj).inv.app F ≫
          quotientMapAlong p₀ u₀ j) a) ≫
      ((Scheme.Modules.pullbackComp a j).app L₀ ≪≫ (Scheme.Modules.pullbackCongr e).app L₀).hom =
    hF.hom ≫ (Scheme.Modules.pullbackCongr hg).inv.app F ≫ quotientMapAlong p₀ u₀ g := by
  have e2 : (Scheme.Modules.pullback a).map (quotientMapAlong p₀ u₀ j) ≫
      (Scheme.Modules.pullbackComp a j).hom.app L₀ =
      (Scheme.Modules.pullbackComp a (j ≫ p₀)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Category.assoc a j p₀)).inv.app F ≫
        quotientMapAlong p₀ u₀ (a ≫ j) := by
    rw [quotientMapAlong_comp p₀ u₀ a j]
    simp
  have e3 := pullbackComp_inv_app_congr_right a hj.symm F
  rw [pullbackCongr_symm_hom hj] at e3
  have e4 := quotientMapAlong_congr p₀ u₀ e
  rw [quotientMapAlong_eq p _ a]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% e3, reassoc_of% e2, e4]
  simp [Scheme.Modules.pullbackCongr]

/-- The quotient map induced along the identity, read out of `p^*F` and followed by the unit
comparison, is the given map. -/
theorem quotientMapAlong_id_quotient (hp : 𝟙 P ≫ p = p) :
    (𝟙 _ ≫ (Scheme.Modules.pullbackCongr hp).inv.app F ≫ quotientMapAlong p u (𝟙 P)) ≫
      ((Scheme.Modules.pullbackId P).app L).hom = u := by
  rw [Category.id_comp, Category.assoc, Iso.app_hom, quotientMapAlong_id]
  simp [Scheme.Modules.pullbackCongr]

end QuotientMapAlong

end Stacks.Modules

namespace Stacks.RelativeProj

open Stacks.Divisors Stacks.Modules Stacks.SymGraded

variable {X T : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent] {f : T ⟶ X}
  (F' : T.Modules) [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj F)

/-! ### The bijection on `Stacks.RelativeProj.projectiveBundle` -/

/-- The tautological quotient pulled back along a morphism over the base is the induced map
along it, read out of `f^*F`. -/
theorem TautologicalDatum.overQuotientMap_eq (D : TautologicalDatum X F)
    (h : T ⟶ projectiveBundle X F) (hh : h ≫ projectiveBundleToBase X F = f) :
    D.overQuotientMap h hh =
      (Scheme.Modules.pullbackCongr hh).inv.app F ≫
        quotientMapAlong (projectiveBundleToBase X F) D.univ h :=
  rfl

/-- **The morphisms `T ⟶ 𝐏(F)` over `f : T ⟶ X` are the invertible quotients of `f^*F`, up to
isomorphism**, for any quasi-coherent `F'` on `T` identified with `f^*F`. It is the cartesian
square bijection `Stacks.RelativeProj.overMorphismEquivSection` followed by [Stacks, Tag 0B3V]'s
bijection `Stacks.RelativeProj.projectiveBundleSectionsEquiv` on `𝐏(F')`. No hypothesis. -/
def projectiveBundleOverEquiv :
    { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f } ≃
      InvertibleQuotientClass T F' :=
  (overMorphismEquivSection F' hF).trans projectiveBundleSectionsEquiv

/-- **The section of the base-changed bundle attached to a morphism over the base classifies the
quotient that the morphism pulls back from the tautological quotient of `𝐏(F)`.** The comparison
of quotient modules is `σ^*` of the identification of tautological twists
`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso`, followed by `σ^*b^* ≅ h^*`; its
compatibility with the quotient maps is
`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec'` together with
`Stacks.Modules.section_quotient_comparison`. -/
theorem pullbackQuotient_isEquivalent_overQuotient (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) :
    ((tautologicalDatum F').pullbackQuotient (overMorphismEquivSection F' hF ⟨h, hh⟩).1
        (overMorphismEquivSection F' hF ⟨h, hh⟩).2).IsEquivalent
      ((tautologicalDatum F).overQuotient F' hF h hh) := by
  set σ := overMorphismEquivSection F' hF ⟨h, hh⟩
  have hσb : σ.1 ≫ projectiveBundleBaseChange f F F' hF = h :=
    (isPullback_projectiveBundleBaseChange f F F' hF).lift_fst _ _ _
  have hb := projectiveBundleBaseChange_comp_projectiveBundleToBase f F F' hF
  have hβ : (Scheme.Modules.pullback (projectiveBundleBaseChange f F F' hF)).map
        (tautologicalDatumUniv F) ≫ (tautologicalDatumTwistBaseChangeIso f F F' hF).hom =
      (Scheme.Modules.pullbackComp (projectiveBundleBaseChange f F F' hF)
          (projectiveBundleToBase X F)).hom.app F ≫
        (Scheme.Modules.pullbackCongr hb).hom.app F ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase T F') f).inv.app F ≫
        (Scheme.Modules.pullback (projectiveBundleToBase T F')).map hF.inv ≫
        tautologicalDatumUniv F' := by
    rw [tautologicalDatumTwistBaseChangeIso_spec', tautologicalBaseChangeIso_hom]
    simp only [Category.assoc]
  exact ⟨(Scheme.Modules.pullback σ.1).mapIso
      (tautologicalDatumTwistBaseChangeIso f F F' hF).symm ≪≫
    (Scheme.Modules.pullbackComp σ.1 (projectiveBundleBaseChange f F F' hF)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hσb).app _,
    section_quotient_comparison F' hF _ _ _ hb (tautologicalDatumUniv F)
      (tautologicalDatumUniv F') (tautologicalDatumTwistBaseChangeIso f F F' hF) hβ σ.1 σ.2 h
      hσb hh⟩

/-- **The bijection is normalised by the tautological quotient**: a morphism `h : T ⟶ 𝐏(F)` over
`f` goes to the class of the invertible quotient `F' ≅ f^*F ≅ h^*π^*F ⟶ h^*𝒪(1)` that it pulls
back from the tautological quotient `π^*F ⟶ 𝒪(1)` of `𝐏(F)`. -/
theorem projectiveBundleOverEquiv_apply
    (h : { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f }) :
    projectiveBundleOverEquiv F' hF h =
      Quotient.mk (invertibleQuotientSetoid T F')
        ((tautologicalDatum F).overQuotient F' hF h.1 h.2) :=
  Quotient.sound (pullbackQuotient_isEquivalent_overQuotient F' hF h.1 h.2)

/-- **The bijection, spelled out**: `h` goes to the class of `Q` exactly when there is an
isomorphism `h^*𝒪(1) ≅ Q.L` carrying the pulled-back tautological quotient to `Q.q`. -/
theorem projectiveBundleOverEquiv_eq_iff
    (h : { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f })
    (Q : InvertibleQuotient T F') :
    projectiveBundleOverEquiv F' hF h = Quotient.mk (invertibleQuotientSetoid T F') Q ↔
      ∃ α : (Scheme.Modules.pullback h.1).obj (tautologicalDatumTwist F) ≅ Q.L,
        hF.hom ≫ (tautologicalDatum F).overQuotientMap h.1 h.2 ≫ α.hom = Q.q := by
  rw [projectiveBundleOverEquiv_apply]
  exact Quotient.eq.trans (exists_congr fun α =>
    Iff.of_eq (congrArg (· = Q.q) (Category.assoc _ _ _)))

section Naturality

variable {T' : Scheme.{u}} (k : T' ⟶ T) (F'' : T'.Modules) [F''.IsQuasicoherent]
  (hF'' : F'' ≅ (Scheme.Modules.pullback k).obj F')

/-- **The bijection is natural in the test scheme**: for `k : T' ⟶ T` and `F'' ≅ k^*F'`, the
bijection at `k ≫ f` sends `k ≫ h` to the base change along `k` of the class that the bijection
at `f` assigns to `h`. The identification of `F''` with `(k ≫ f)^*F` is the one through
`k^*F' ≅ k^*f^*F`. -/
theorem projectiveBundleOverEquiv_comp
    (h : { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f }) :
    projectiveBundleOverEquiv F''
        (hF'' ≪≫ (Scheme.Modules.pullback k).mapIso hF ≪≫
          (Scheme.Modules.pullbackComp k f).app F)
        ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass k hF''
        (projectiveBundleOverEquiv F' hF h) := by
  rw [projectiveBundleOverEquiv_apply, projectiveBundleOverEquiv_apply,
    Stacks.ProjectiveBundleQuotients.baseChangeClass_mk]
  exact Quotient.sound ⟨((Scheme.Modules.pullbackComp k h.1).app _).symm,
    quotientMapAlong_comp_baseChange (projectiveBundleToBase X F) (tautologicalDatum F).univ F'
      hF k F'' hF'' h.1 h.2 _⟩

end Naturality

/-! ### The `SheafGradedAlgebra` presentation of the bundle -/

/-- **The morphisms into the two presentations of `𝐏(F)` over the base correspond**, through the
comparison `Stacks.RelativeProj.bundlePresentationIso`. -/
def symGradedOverMorphismEquiv :
    { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f } ≃
      { h : T ⟶ projectiveBundle X F // h ≫ projectiveBundleToBase X F = f } where
  toFun g := ⟨g.1 ≫ (bundlePresentationIso F).hom, by
    rw [Category.assoc, bundlePresentationIso_hom_comp_toBase, g.2]⟩
  invFun h := ⟨h.1 ≫ (bundlePresentationIso F).inv, by
    rw [Category.assoc, bundlePresentationIso_inv_comp_toBase, h.2]⟩
  left_inv g := Subtype.ext (by simp)
  right_inv h := Subtype.ext (by simp)

/-- The morphism `symGradedOverMorphismEquiv` attaches to `g` is the composite of `g` with
`(bundlePresentationIso F).hom`. -/
@[simp] theorem symGradedOverMorphismEquiv_apply_coe
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f }) :
    (symGradedOverMorphismEquiv g).1 = g.1 ≫ (bundlePresentationIso F).hom :=
  rfl

/-- **The invertible quotient of `F'` that a morphism `g : T ⟶ Proj_X(Sym F)` over the base pulls
back from the tautological map** `Stacks.ProjectiveBundleSplitting.tautologicalMap`
`π^*F ⟶ 𝒪(1)` of the `SheafGradedAlgebra` presentation:
`F' ≅ f^*F ≅ g^*π^*F ⟶ g^*𝒪(1)`. -/
def symGradedOverQuotient (g : T ⟶ (symGradedBundle F).scheme)
    (hg : g ≫ (symGradedBundle F).toBase = f) : InvertibleQuotient T F' where
  L := (Scheme.Modules.pullback g).obj
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
      (isQuasicoherentPieces_of_isQuasicoherent F))
  invertible :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ g _
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
          (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist F
            (isQuasicoherentPieces_of_isQuasicoherent F))))
  q := hF.hom ≫ (Scheme.Modules.pullbackCongr hg).inv.app F ≫
    quotientMapAlong (symGradedBundle F).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F)) g
  epi :=
    haveI : Epi (Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F)) :=
      Stacks.ProjectiveBundleSplitting.epi_tautologicalMap F _
    inferInstance

/-- **The morphisms `T ⟶ Proj_X(Sym F)` over `f : T ⟶ X` are the invertible quotients of
`f^*F`, up to isomorphism**, on the `SheafGradedAlgebra` presentation of the projective bundle. -/
def symGradedOverEquiv :
    { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f } ≃
      InvertibleQuotientClass T F' :=
  symGradedOverMorphismEquiv.trans (projectiveBundleOverEquiv F' hF)

/-- **The bijection is normalised by the tautological map**
`Stacks.ProjectiveBundleSplitting.tautologicalMap : π^*F ⟶ 𝒪(1)`: a morphism `g` over `f` goes to
the class of the quotient `Stacks.RelativeProj.symGradedOverQuotient` it pulls back. -/
theorem symGradedOverEquiv_apply
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f }) :
    symGradedOverEquiv F' hF g =
      Quotient.mk (invertibleQuotientSetoid T F') (symGradedOverQuotient F' hF g.1 g.2) := by
  refine (projectiveBundleOverEquiv_apply F' hF _).trans (Quotient.sound ?_)
  have e : (g.1 ≫ (bundlePresentationIso F).hom) ≫ (bundlePresentationIso F).inv = g.1 := by
    simp
  exact ⟨(Scheme.Modules.pullbackComp _ (bundlePresentationIso F).inv).app _ ≪≫
      (Scheme.Modules.pullbackCongr e).app _,
    quotientMapAlong_presentation (projectiveBundleToBase X F) F' hF (symGradedBundle F).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F))
      (bundlePresentationIso F).inv (bundlePresentationIso_inv_comp_toBase F) _
      (symGradedOverMorphismEquiv g).2 g.1 e g.2⟩

/-- **The bijection on the `SheafGradedAlgebra` presentation, spelled out**: `g` goes to the
class of `Q` exactly when there is an isomorphism `g^*𝒪(1) ≅ Q.L` carrying the quotient map that
`g` pulls back from the tautological map to `Q.q`. -/
theorem symGradedOverEquiv_eq_iff
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f })
    (Q : InvertibleQuotient T F') :
    symGradedOverEquiv F' hF g = Quotient.mk (invertibleQuotientSetoid T F') Q ↔
      ∃ α : (Scheme.Modules.pullback g.1).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
            (isQuasicoherentPieces_of_isQuasicoherent F)) ≅ Q.L,
        hF.hom ≫ (Scheme.Modules.pullbackCongr g.2).inv.app F ≫
            quotientMapAlong (symGradedBundle F).toBase
              (Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)) g.1 ≫ α.hom = Q.q := by
  rw [symGradedOverEquiv_apply]
  exact Quotient.eq.trans (exists_congr fun α =>
    Iff.of_eq (congrArg (· = Q.q) ((Category.assoc _ _ _).trans
      (congrArg (hF.hom ≫ ·) (Category.assoc _ _ _)))))

section Naturality

variable {T' : Scheme.{u}} (k : T' ⟶ T) (F'' : T'.Modules) [F''.IsQuasicoherent]
  (hF'' : F'' ≅ (Scheme.Modules.pullback k).obj F')

/-- **The bijection on the `SheafGradedAlgebra` presentation is natural in the test scheme.** -/
theorem symGradedOverEquiv_comp
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f }) :
    symGradedOverEquiv F''
        (hF'' ≪≫ (Scheme.Modules.pullback k).mapIso hF ≪≫
          (Scheme.Modules.pullbackComp k f).app F)
        ⟨k ≫ g.1, by rw [Category.assoc, g.2]⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass k hF''
        (symGradedOverEquiv F' hF g) := by
  have h1 : symGradedOverMorphismEquiv (f := k ≫ f) ⟨k ≫ g.1, by rw [Category.assoc, g.2]⟩ =
      ⟨k ≫ (symGradedOverMorphismEquiv g).1, by
        rw [Category.assoc, (symGradedOverMorphismEquiv g).2]⟩ :=
    Subtype.ext (Category.assoc _ _ _)
  have h2 := projectiveBundleOverEquiv_comp F' hF k F'' hF'' (symGradedOverMorphismEquiv g)
  rwa [← h1] at h2

end Naturality

section Universal

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

variable (F)

/-- **The tautological quotient of the `SheafGradedAlgebra` presentation**, the surjection
`Stacks.ProjectiveBundleSplitting.tautologicalMap : π^*F ⟶ 𝒪(1)` onto the invertible twist, as an
invertible quotient of `π^*F`. -/
def symGradedTautologicalQuotient :
    InvertibleQuotient (symGradedBundle F).scheme
      ((Scheme.Modules.pullback (symGradedBundle F).toBase).obj F) where
  L := Stacks.ProjectiveBundleSplitting.tautologicalTwist F
    (isQuasicoherentPieces_of_isQuasicoherent F)
  invertible := Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist F
    (isQuasicoherentPieces_of_isQuasicoherent F)
  q := Stacks.ProjectiveBundleSplitting.tautologicalMap F
    (isQuasicoherentPieces_of_isQuasicoherent F)
  epi := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap F _

/-- **The universal quotient is the tautological one**: under the bijection at the projection
`π` itself, the identity of the bundle corresponds to the class of the tautological surjection
`π^*F ⟶ 𝒪(1)`. -/
theorem symGradedOverEquiv_id :
    symGradedOverEquiv ((Scheme.Modules.pullback (symGradedBundle F).toBase).obj F) (Iso.refl _)
        ⟨𝟙 _, Category.id_comp _⟩ =
      Quotient.mk (invertibleQuotientSetoid _ _) (symGradedTautologicalQuotient F) := by
  rw [symGradedOverEquiv_apply]
  exact Quotient.sound ⟨(Scheme.Modules.pullbackId _).app _,
    quotientMapAlong_id_quotient (symGradedBundle F).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F)) _⟩

end Universal

end Stacks.RelativeProj

end
