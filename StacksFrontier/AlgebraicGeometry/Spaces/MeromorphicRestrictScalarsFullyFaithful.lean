module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicUnitModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalizationPushforward

/-!
# Restriction of scalars along a localization of the structure sheaf is fully faithful

Let `X` be a ringed site and `S` a multiplicative subpresheaf of its structure sheaf, and let
`θ : 𝒪_X ⟶ S⁻¹𝒪_X` be the canonical map of Stacks 0EMC into the sheafified sectionwise
localization.  Restriction of scalars along `θ` is **fully faithful**: an `𝒪_X`-linear morphism
between two `S⁻¹𝒪_X`-modules is automatically `S⁻¹𝒪_X`-linear.

The reason is the reason it holds for modules over a localization of a ring: a section of
`S⁻¹𝒪_X` is locally the image of a fraction `a/s`, and on the sections over such an object the
map is linear for `a/s` because `s` acts invertibly on both sides and the map is `𝒪_X`-linear.
Separatedness of the target then upgrades the local statement to the sections over the object
one started from.

Applied to the sheaf of meromorphic functions `𝒦_X` of Stacks 0EN3, which is by construction
the sheafified localization at the regular sections, this says that
`AlgebraicGeometry.Space.meromorphicRestrictScalars` is fully faithful.  The consequence this is
for: an isomorphism of the `𝒪_X`-modules underlying two `𝒦_X`-modules comes from an isomorphism
of `𝒦_X`-modules.  That is what lets the description of `𝒦_X` and of `𝒦_X(M)` at the
codimension-zero points — a statement about `𝒪_X`-modules, since the comparison of Stacks 0ENA
is one of `𝒪_X`-modules — be read as an isomorphism `𝒦_X ≅ 𝒦_X(M)` of `𝒦_X`-modules, which is
the form the construction of a regular meromorphic section of Stacks 0EPQ consumes.

Note that this is strictly stronger than
`Stacks.SheafOfModules.ChangeOfRings.reflectsIsomorphisms_restrictScalars`, which promotes an
isomorphism *of a given morphism* and cannot identify two objects; and it is not an instance of
`Stacks.SheafOfModules.ChangeOfRings.full_restrictScalars`, whose hypothesis is local
surjectivity of the map of sheaves of rings — `𝒪_X ⟶ 𝒦_X` is not locally surjective, its
sections being fractions and not regular functions.

## Main definitions

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.fullyFaithfulRestrictScalars`:
  restriction of scalars along the canonical map into the sheafified localization is fully
  faithful.
* `AlgebraicGeometry.Space.fullyFaithfulMeromorphicRestrictScalars`: the same for
  `𝒪_X ⟶ 𝒦_X`.

## Main results

* `AlgebraicGeometry.Space.nonempty_iso_of_nonempty_iso_meromorphicRestrictScalars`: two
  `𝒦_X`-modules whose underlying `𝒪_X`-modules are isomorphic are isomorphic.
* `AlgebraicGeometry.Space.nonempty_iso_meromorphicSectionSheaf_of_nonempty_iso_meromorphicModule`:
  **an isomorphism of `𝒪_X`-modules `𝒦_X ≅ 𝒦_X(M)` gives an isomorphism of `𝒦_X`-modules**, the
  reading of Stacks 0ENA that Stacks 0EPQ consumes.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe m w v u

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

/-- **A morphism of modules over a localization that is linear over the base ring is linear over
the localization.**  Write a section of the localization as `a / s`; then `s` acts invertibly on
the target, and the two sides agree after multiplication by the image of `s`, because the map is
linear over the base ring. -/
theorem map_smul_of_isLocalization {R₀ A K : Type*} [CommRing R₀] [CommRing A] [Ring K]
    (Sub : Submonoid R₀) [Algebra R₀ A] [IsLocalization Sub A]
    (κ : A →+* K) (θ : R₀ →+* K) (hθ : ∀ r : R₀, κ (algebraMap R₀ A r) = θ r)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]
    (f : M → N) (hf : ∀ (r : R₀) (y : M), f (θ r • y) = θ r • f y)
    (a : A) (x : M) : f (κ a • x) = κ a • f x := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj Sub a
  obtain ⟨e, he⟩ := (IsLocalization.map_units A s).map κ
  have hs : θ s.1 * κ a = θ r := by
    rw [← hθ s.1, ← hθ r, ← map_mul, mul_comm, h]
  have hi : Function.Injective fun y : N => θ s.1 • y := by
    have ht : (e : K) = θ s.1 := he.trans (hθ s.1)
    rw [← ht]
    exact MulAction.injective e
  refine hi ?_
  calc θ s.1 • f (κ a • x) = f (θ s.1 • (κ a • x)) := (hf s.1 _).symm
    _ = f (θ r • x) := by rw [smul_smul, hs]
    _ = θ r • f x := hf r x
    _ = θ s.1 • (κ a • f x) := by rw [smul_smul, hs]

variable {X : RingedSite.{u, v, w}} (S : MultiplicativeSubpresheaf X)
  [HasWeakSheafify X.J CommRingCat.{w}]

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **Restriction of scalars along the canonical map `𝒪_X ⟶ S⁻¹𝒪_X` of Stacks 0EMC is fully
faithful.**  An `𝒪_X`-linear morphism of `S⁻¹𝒪_X`-modules is `S⁻¹𝒪_X`-linear: a section of
`S⁻¹𝒪_X` is locally a fraction, and over such an object linearity for a fraction follows from
linearity over `𝒪_X` because the denominator acts invertibly. -/
noncomputable def fullyFaithfulRestrictScalars :
    (SheafOfModules.restrictScalars.{m}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        S.toLocalizationSheaf)).FullyFaithful := by
  let K := (presheafToSheaf X.J CommRingCat.{w}).obj S.localizationPresheaf
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let α := (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map S.toLocalizationSheaf
  let κ := toSheafify X.J S.localizationPresheaf
  have hκ : Presheaf.IsLocallySurjective X.J κ :=
    (X.J.W_toSheafify S.localizationPresheaf).isLocallySurjective
  have hθ (V : X.Cᵒᵖ) :
      (κ.app V).hom.comp
          (algebraMap (X.O.obj.obj V) (S.localizationPresheaf.obj V)) =
        (S.toLocalizationSheaf.hom.app V).hom :=
    (congrArg (fun f : X.O.obj ⟶ K.obj => (f.app V).hom) S.toLocalizationSheaf_hom).symm
  let R := (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj K
  let pre {M N : SheafOfModules.{m} R}
      (f : (SheafOfModules.restrictScalars.{m} α).obj M ⟶
        (SheafOfModules.restrictScalars.{m} α).obj N) : M ⟶ N := by
    refine ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf O.obj).map f.val) ?_⟩
    intro V a x
    apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem X.J κ a)
    rintro W g ⟨b, hb⟩
    have hθW : ∀ r : X.O.obj.obj (op W),
        (show Localization (S.obj (op W)) →+* R.obj.obj (op W) from (κ.app (op W)).hom)
            (algebraMap (X.O.obj.obj (op W)) (Localization (S.obj (op W))) r) =
          (α.hom.app (op W)).hom r :=
      fun r => congrFun (congrArg (fun φ : _ →+* _ => φ.toFun) (hθ (op W))) r
    have hfW : ∀ (r : X.O.obj.obj (op W)) (y : M.val.obj (op W)),
        (show N.val.obj (op W) from
            f.val.app (op W) ((α.hom.app (op W)).hom r • (show M.val.obj (op W) from y))) =
          (α.hom.app (op W)).hom r • (show N.val.obj (op W) from f.val.app (op W) y) :=
      fun r y => (f.val.app (op W)).hom.map_smul r y
    have hbR : R.obj.map g.op a =
        (show Localization (S.obj (op W)) →+* R.obj.obj (op W) from (κ.app (op W)).hom) b :=
      hb.symm
    have h1 : N.val.map g.op (f.val.app V (a • x)) =
        f.val.app (op W) (M.val.map g.op (a • x)) :=
      (PresheafOfModules.naturality_apply f.val g.op (a • x)).symm
    have h2 : M.val.map g.op (a • x) =
        R.obj.map g.op a • (show M.val.obj (op W) from M.val.map g.op x) :=
      M.val.map_smul g.op a x
    have h3 : N.val.map g.op (a • (show N.val.obj V from f.val.app V x)) =
        R.obj.map g.op a •
          (show N.val.obj (op W) from N.val.map g.op (f.val.app V x)) :=
      N.val.map_smul g.op a _
    have h4 : N.val.map g.op (f.val.app V x) =
        f.val.app (op W) (M.val.map g.op x) :=
      (PresheafOfModules.naturality_apply f.val g.op x).symm
    have h5 : f.val.app (op W) (R.obj.map g.op a •
          (show M.val.obj (op W) from M.val.map g.op x)) =
        R.obj.map g.op a •
          (show N.val.obj (op W) from f.val.app (op W) (M.val.map g.op x)) := by
      rw [hbR]
      exact map_smul_of_isLocalization (S.obj (op W))
        (show Localization (S.obj (op W)) →+* R.obj.obj (op W) from (κ.app (op W)).hom)
        (α.hom.app (op W)).hom hθW
        (fun y : M.val.obj (op W) => show N.val.obj (op W) from f.val.app (op W) y)
        hfW b _
    change N.val.map g.op (f.val.app V (a • x)) =
      N.val.map g.op (a • (show N.val.obj V from f.val.app V x))
    rw [h1, h2, h5, h3, h4]
  refine { preimage := @pre, map_preimage := ?_, preimage_map := ?_ }
  · intros
    ext V x
    rfl
  · intros
    ext V x
    rfl

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

namespace AlgebraicGeometry.Space

universe uu

variable (B : BigFppfSite.{uu}) (S : Scheme.{uu}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type uu) (hF : IsAlgebraicSpace B S hS F)

/-- **Restriction of scalars from `𝒦_X`-modules to `𝒪_X`-modules is fully faithful**: `𝒦_X` is
the sheafified localization of `𝒪_X` at its regular sections, and an `𝒪_X`-linear morphism of
modules over a localization is linear over the localization. -/
noncomputable def fullyFaithfulMeromorphicRestrictScalars :
    (meromorphicRestrictScalars B S hS F hF).FullyFaithful := by
  let : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective CommRingCat.{uu} := by
    change (SmallEtale.topology B S hS F).WEqualsLocallyBijective CommRingCat.{uu}
    infer_instance
  exact RingedSite.MultiplicativeSubpresheaf.fullyFaithfulRestrictScalars
    (regularSectionsSubpresheaf B S hS F hF)

/-- **Two `𝒦_X`-modules whose underlying `𝒪_X`-modules are isomorphic are isomorphic.** -/
theorem nonempty_iso_of_nonempty_iso_meromorphicRestrictScalars
    (N₁ N₂ : SheafOfModules.{uu + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O))
    (h : Nonempty ((meromorphicRestrictScalars B S hS F hF).obj N₁ ≅
      (meromorphicRestrictScalars B S hS F hF).obj N₂)) :
    Nonempty (N₁ ≅ N₂) :=
  h.map (fullyFaithfulMeromorphicRestrictScalars B S hS F hF).preimageIso

/-- **An isomorphism of `𝒪_X`-modules `𝒦_X ≅ 𝒦_X(M)` is an isomorphism of `𝒦_X`-modules.**

The left-hand side is `AlgebraicGeometry.Space.meromorphicModule`, the source of the comparison
of the first conclusion of Stacks 0ENA, and the right-hand side is
`AlgebraicGeometry.Space.meromorphicSectionSheafAsModule`, the target of the comparison of its
second conclusion; both are `𝒪_X`-modules, while the construction of a regular meromorphic
section of Stacks 0EPQ consumes an isomorphism of `𝒦_X`-modules.  Restriction of scalars along
`𝒪_X ⟶ 𝒦_X` is fully faithful, so the two readings carry the same isomorphisms. -/
theorem nonempty_iso_meromorphicSectionSheaf_of_nonempty_iso_meromorphicModule
    (X : AlgebraicSpaces B S hS) (M : Modules.{uu, uu} B S hS X.1 X.2)
    (h : Nonempty (meromorphicModule B S hS X ≅
      meromorphicSectionSheafAsModule B S hS X.1 X.2 M)) :
    Nonempty (SheafOfModules.uliftObj.{_, _, _, _, uu + 1}
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O)) ≅
      meromorphicSectionSheaf.{uu, uu} B S hS X.1 X.2 M) := by
  refine nonempty_iso_of_nonempty_iso_meromorphicRestrictScalars B S hS X.1 X.2 _ _ ?_
  refine h.map fun e => ?_
  exact (eqToIso (meromorphicRestrictScalars_obj_uliftUnit B S hS X.1 X.2)).trans e

end AlgebraicGeometry.Space

end
