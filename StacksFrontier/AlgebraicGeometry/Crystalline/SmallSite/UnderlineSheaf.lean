module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiRingedComparison

/-!
# The sheaves `G̲` on the small crystalline site, and the module `F̲`

Fix a global crystalline situation `(p, (S, I, γ), X)`.  For a sheaf `G` on the small Zariski site
`X_Zar` of `X`, section 60.10 of the chapter attaches a sheaf `G̲` on the small crystalline site
`Cris(X/S)` by

  `G̲(U, T, δ) = G(U)`,

`U` being read as the open image of the structure map `U ⟶ X`, which is an open immersion by
[Stacks, Tag 07IG].  This is restriction along the forgetful functor `(U, T, δ) ↦ U` of
[Stacks, Tag 07IH], so `G̲` is a presheaf with no further work; that it is a *sheaf* is the
continuity of that functor, which is proved here.

Taking `G = 𝒪_X` gives `G_a̲ : (U, T, δ) ↦ Γ(U, 𝒪_U)` together with the surjection
`𝒪_{X/S} ⟶ G_a̲` whose component at `(U, T, δ)` is restriction along the closed immersion
`U ↪ T`, that is
`Crystalline.GlobalCrystallineSituation.SmallSite.crisRingToZariskiInverseImage`; for a
quasi-coherent `𝒪_X`-module `F` the sheaf `F̲` is an `𝒪_{X/S}`-module through that ring map.

The point of the construction is [Stacks, Tag 07LN]: `F̲` is not a crystal, but it does satisfy
conditions (1) and (2) of [Stacks, Tag 07JN], so the vanishing clause of that proposition applies
to it.  Both conditions are proved here with no hypothesis beyond the quasi-coherence of `F`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `underlinePresheaf` and `underlineSheaf` — the presheaf `G̲` on `Cris(X/S)` attached to a
  presheaf `G` on the opens of `X`, and the sheaf it is when `G` is a sheaf.
* `underlineCommRingSheaf` and `underlineRingSheaf` — **`G_a̲ = 𝒪_X̲`**, in commutative rings and
  in rings.  The underlying presheaves are the existing `zariskiInverseImageCommRing` and
  `zariskiInverseImageRing`; what is added is the sheaf condition.
* `underlineModules` — **`F̲` for an `𝒪_X`-module `F`**, as a sheaf of `𝒪_{X/S}`-modules on
  `Cris(X/S)`.

## Main results

* `compatiblePreserving_forgetToOpens`, `coverPreserving_forgetToOpens` and
  `forgetToOpens_isContinuous` — **the forgetful functor `Cris(X/S) ⟶ X_Zar` of
  [Stacks, Tag 07IH] is continuous** in the sense of `CategoryTheory.Functor.IsContinuous`, so
  restriction along it carries sheaves to sheaves.
* `structureToZariskiInverseImage_restrictOpen` — the ring comparison `𝒪_{X/S} ⟶ G_a̲` at a
  restriction `(U ∩ W, W, δ|_W)` is the map on sections of the closed immersion `U ↪ T` followed
  by the identification of `Γ(U ∩ W, 𝒪_U)` with the sections of `𝒪_X` over its image.
* `underlineRestrictionIso` — the restriction of `F̲` to the ambient scheme `T` of `(U, T, δ)` is
  the direct image along `U ↪ T` of the restriction of `F` to `U`.
* `isLocallyQuasiCoherent_underlineModules` — **condition (1) of [Stacks, Tag 07JN] for `F̲`**,
  `F` quasi-coherent.
* `isSurjectiveComparison_underlineModules` — **condition (2) of [Stacks, Tag 07JN] for `F̲`**.

## Implementation notes

The continuity of `Crystalline.GlobalCrystallineSituation.forgetToOpens` is obtained from
`CategoryTheory.Functor.isContinuous_of_coverPreserving`, whose two halves are proved directly.
The compatible-preserving half is the adjunction `opensFree ⊣ forgetToOpens` of
[Stacks, Tag 07II]: a compatible family is tested against a pair of morphisms out of an open `V`
of `X`, and `V` is the thickened scheme of the object `(V, V, ∅)` of [Stacks, Tag 07I8], out of
which a morphism is unique (`opensFree_hom_ext`), so the compatibility of the family applies
verbatim.  The cover-preserving half is an induction over
`CategoryTheory.Coverage.Saturate` along `restrictCoverage_toGrothendieck`, whose generating case
is `forgetToOpens_zariskiCovering_functorPushforward_mem` of [Stacks, Tag 07IL].  Both
halves use repeatedly that the hom sets of `X.Opens` are subsingletons, which is what makes every
diagram of opens commute.

The module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` explains why
the
ring comparison runs from `𝒪_{X/S}` to `G_a̲` and not the other way, and therefore why `F̲` is an
`𝒪_{X/S}`-module rather than `𝒪_{X/S}` being a `G_a̲`-algebra.

## References

* [Stacks Project, Tag 07IN](https://stacks.math.columbia.edu/tag/07IN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w v t u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The forgetful functor is continuous -/

/-- **The forgetful functor `Cris(X/S) ⟶ X_Zar` of [Stacks, Tag 07IH] preserves compatible
families.**  A compatible family of elements over a presieve of `Cris(X/S)` is tested against a
pair of morphisms `V ⟶ U₁`, `V ⟶ U₂` of opens of `X` with a common composite; the open `V` is the
thickened scheme of the object `(V, V, ∅)` of [Stacks, Tag 07I8], and by the adjunction
`opensFree ⊣ forgetToOpens` of [Stacks, Tag 07II] the two morphisms of opens lift to morphisms of
`Cris(X/S)` out of `(V, V, ∅)`, which have equal composites because a morphism out of `(V, V, ∅)`
is unique.  The compatibility of the family at that pair is then exactly what is asked, the two
triangles of opens commuting because the hom sets of `X.Opens` are subsingletons. -/
theorem compatiblePreserving_forgetToOpens (S : GlobalCrystallineSituation.{u}) :
    CompatiblePreserving.{w} (Opens.grothendieckTopology S.X.carrier) (forgetToOpens S) where
  compatible := by
    intro ℱ Z T x hx Y₁ Y₂ V f₁ f₂ g₁ g₂ hg₁ hg₂ _he
    have hle : V ≤ (forgetToOpens S).obj ((opensFree S).obj V) :=
      ((Scheme.Opens.opensRange_ι V).ge : _)
    set h₁ : (opensFree S).obj V ⟶ Y₁ :=
      ((opensFreeForgetAdjunction S).homEquiv V Y₁).symm f₁
    set h₂ : (opensFree S).obj V ⟶ Y₂ :=
      ((opensFreeForgetAdjunction S).homEquiv V Y₂).symm f₂
    have e₁ : f₁ = homOfLE hle ≫ (forgetToOpens S).map h₁ := Subsingleton.elim _ _
    have e₂ : f₂ = homOfLE hle ≫ (forgetToOpens S).map h₂ := Subsingleton.elim _ _
    rw [e₁, e₂]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact congrArg _ (hx h₁ h₂ hg₁ hg₂ (opensFree_hom_ext _ _))

/-- **The forgetful functor `Cris(X/S) ⟶ X_Zar` of [Stacks, Tag 07IH] is cover-preserving:** the
image of a covering sieve of the small crystalline site is a covering sieve of the small Zariski
site of `X`.

The Zariski topology of `Cris(X/S)` is generated by the coverage of families of restrictions of an
object to an open cover of its ambient scheme, `restrictCoverage_toGrothendieck`, so the covering
sieves are described inductively by `CategoryTheory.Coverage.Saturate` and there are three cases:
the generating families, where this is
`forgetToOpens_zariskiCovering_functorPushforward_mem` of [Stacks, Tag 07IL]; the maximal sieve,
whose image contains an identity; and the local character, where a point is first put in an open
coming from the outer sieve and then, that open meeting the image of the object indexing it, in an
open coming from the pullback of the inner sieve. -/
theorem coverPreserving_forgetToOpens (S : GlobalCrystallineSituation.{u}) :
    CoverPreserving (smallTopology S) (Opens.grothendieckTopology S.X.carrier)
      (forgetToOpens S) where
  cover_preserve {A} {R} hR := by
    rw [← restrictCoverage_toGrothendieck] at hR
    induction hR with
    | of A R' hR' =>
        obtain ⟨I, V, hV, rfl⟩ := hR'
        exact forgetToOpens_zariskiCovering_functorPushforward_mem S (A.restrictOpenCover V)
          (CrystallineThickening.isZariskiCovering_restrictOpenCover A V hV)
    | top A =>
        rw [Opens.mem_grothendieckTopology]
        intro y hy
        exact ⟨(forgetToOpens S).obj A, homOfLE le_rfl,
          ⟨A, 𝟙 A, homOfLE le_rfl, trivial, Subsingleton.elim _ _⟩, hy⟩
    | transitive A R₁ R₂ _h₁ _h₂ ih₁ ih₂ =>
        rw [Opens.mem_grothendieckTopology]
        intro y hy
        obtain ⟨V₁, m₁, hm₁, hyV₁⟩ := (Opens.mem_grothendieckTopology _).1 ih₁ y hy
        obtain ⟨Z, k, n, hk, -⟩ := hm₁
        obtain ⟨V₂, m₂, hm₂, hyV₂⟩ :=
          (Opens.mem_grothendieckTopology _).1 (ih₂ hk) y (leOfHom n hyV₁)
        obtain ⟨Z', k', n', hk', -⟩ := hm₂
        exact ⟨V₂, m₂ ≫ (forgetToOpens S).map k,
          ⟨Z', k' ≫ k, n', hk', Subsingleton.elim _ _⟩, hyV₂⟩

/-- **The forgetful functor `Cris(X/S) ⟶ X_Zar` of [Stacks, Tag 07IH] is continuous**: restriction
along it carries a sheaf on the small Zariski site of `X` to a sheaf on the small crystalline site.
This is `CategoryTheory.Functor.isContinuous_of_coverPreserving` applied to the two halves above,
and it is what makes `G̲` a sheaf. -/
instance forgetToOpens_isContinuous (S : GlobalCrystallineSituation.{u}) :
    (forgetToOpens S).IsContinuous (smallTopology S)
      (Opens.grothendieckTopology S.X.carrier) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_forgetToOpens S)
    (coverPreserving_forgetToOpens S)

/-! ### `G̲` for a sheaf on the Zariski site of `X` -/

/-- **The presheaf `G̲` on the small crystalline site attached to a presheaf `G` on the opens of
`X`**: its sections over an object `(U, T, δ)` of `Cris(X/S)` are the sections of `G` over the open
image of `U` in `X`.  This is restriction along the forgetful functor of [Stacks, Tag 07IH], so the
functoriality is that of `G` along the inclusions of opens. -/
def underlinePresheaf {𝒜 : Type v} [Category.{t} 𝒜] (S : GlobalCrystallineSituation.{u})
    (G : (S.X.Opens)ᵒᵖ ⥤ 𝒜) : (CrystallineThickening S)ᵒᵖ ⥤ 𝒜 :=
  (forgetToOpens S).op ⋙ G

/-- The sections of `G̲` over an object of `Cris(X/S)` are the sections of `G` over the open image
of its thickened scheme in `X`. -/
@[simp]
theorem underlinePresheaf_obj {𝒜 : Type v} [Category.{t} 𝒜] (S : GlobalCrystallineSituation.{u})
    (G : (S.X.Opens)ᵒᵖ ⥤ 𝒜) (A : CrystallineThickening S) :
    (underlinePresheaf S G).obj (op A) = G.obj (op ((forgetToOpens S).obj A)) := rfl

/-- **`G̲` is a sheaf on the small crystalline site when `G` is a sheaf on `X_Zar`**, by the
continuity of the forgetful functor of [Stacks, Tag 07IH]. -/
theorem isSheaf_underlinePresheaf {𝒜 : Type v} [Category.{t} 𝒜]
    (S : GlobalCrystallineSituation.{u}) (G : (S.X.Opens)ᵒᵖ ⥤ 𝒜)
    (hG : Presheaf.IsSheaf (Opens.grothendieckTopology S.X.carrier) G) :
    Presheaf.IsSheaf (smallTopology S) (underlinePresheaf S G) :=
  (forgetToOpens S).op_comp_isSheaf_of_isSheaf _ _ _ hG

/-- **The sheaf `G̲` on the small crystalline site attached to a sheaf `G` on `X_Zar`.** -/
def underlineSheaf {𝒜 : Type v} [Category.{t} 𝒜] (S : GlobalCrystallineSituation.{u})
    (G : Sheaf (Opens.grothendieckTopology S.X.carrier) 𝒜) : Sheaf (smallTopology S) 𝒜 :=
  ⟨underlinePresheaf S G.obj, isSheaf_underlinePresheaf S G.obj G.property⟩

/-- **`G_a̲ = 𝒪_X̲`, as a sheaf of commutative rings on the small crystalline site**: its sections
over `(U, T, δ)` are `Γ(U, 𝒪_U)`.  The underlying presheaf is
`zariskiInverseImageCommRing`, which is `𝒪_X̲` read as the inverse image `u_{X/S}^{-1}𝒪_X`; what
this adds is the sheaf condition. -/
def underlineCommRingSheaf (S : GlobalCrystallineSituation.{u}) :
    Sheaf (smallTopology S) CommRingCat.{u} :=
  ⟨zariskiInverseImageCommRing S,
    isSheaf_underlinePresheaf S S.X.presheaf S.X.sheaf.property⟩

/-- **`G_a̲ = 𝒪_X̲`, as a sheaf of rings on the small crystalline site**, the coefficients in which
the structure sheaf `structureSheaf` of `Cris(X/S)` is stated, so that the ring comparison
`crisRingToZariskiInverseImage` is a map `𝒪_{X/S} ⟶ G_a̲` of sheaves of rings. -/
def underlineRingSheaf (S : GlobalCrystallineSituation.{u}) :
    Sheaf (smallTopology S) RingCat.{u} :=
  ⟨zariskiInverseImageRing S,
    isSheaf_underlinePresheaf S S.X.ringCatSheaf.obj S.X.ringCatSheaf.property⟩

/-! ### `F̲` for a quasi-coherent module on `X` -/

/-- **`F̲` for an `𝒪_X`-module `F`, as a sheaf of `𝒪_{X/S}`-modules on the small crystalline
site.**  Its sections over an object `(U, T, δ)` of `Cris(X/S)` are the sections `F(U)` of `F` over
the open image of `U` in `X`, an `𝒪_{X/S}(U, T, δ) = Γ(T, 𝒪_T)`-module through the ring comparison
`𝒪_{X/S} ⟶ G_a̲` of `crisRingToZariskiInverseImage`, that is through restriction along the closed
immersion `U ↪ T`.  The sheaf condition is the continuity of the forgetful functor of
[Stacks, Tag 07IH]. -/
def underlineModules (S : GlobalCrystallineSituation.{u}) (F : S.X.Modules) :
    SheafOfModules.{u} (structureSheaf S) where
  val := (PresheafOfModules.pushforward.{u} (F := forgetToOpens S)
    (R := S.X.ringCatSheaf.obj) (crisRingToZariskiInverseImage S)).obj F.val
  isSheaf := (forgetToOpens S).op_comp_isSheaf_of_isSheaf _ _ _ F.isSheaf

/-! ### Condition (2) of [Stacks, Tag 07JN] for `F̲` -/

/-- **The open of `X` underlying the restriction of an object of `Cris(X/S)` to an open of its
ambient scheme** is the image in `X` of the preimage of that open in the thickened scheme. -/
theorem forgetToOpens_restrictOpen (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (forgetToOpens S).obj (A.restrictOpen V) =
      A.obj.toX ''ᵁ (A.obj.thickening.immersion ⁻¹ᵁ V) := by
  have := A.property
  change Scheme.Hom.opensRange
    ((A.obj.thickening.immersion ⁻¹ᵁ V).ι ≫ A.obj.toX) = _
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]

section Comparison

variable {A B : CrystallineThickening S}

/-- **An open of the ambient scheme of the target of a morphism of `Cris(X/S)` cutting out a given
open of the ambient scheme of its source, over which the transition map of an underline sheaf is
invertible.**  It is the open of `T'` matching, under the homeomorphism of the thickening
`U' ↪ T'`, the preimage in `U'` of the open of `X` underlying the restriction of the source to the
given open. -/
def comparisonLiftOpen (_g : A ⟶ B) (W : A.obj.thickening.target.scheme.Opens) :
    B.obj.thickening.target.scheme.Opens :=
  B.obj.thickening.isThickening.opensCongr
    (B.obj.toX ⁻¹ᵁ (A.obj.toX ''ᵁ (A.obj.thickening.immersion ⁻¹ᵁ W)))

/-- **`comparisonLiftOpen` does cut out the given open**: its preimage on ambient schemes is that
open.  The two thickenings are homeomorphisms on points, so it is enough to check this after
pulling back to the thickened scheme, where the compatibilities of a morphism of `Cris(X/S)` with
the immersions and with the maps to `X` turn it into the fact that an open immersion recovers an
open from its image. -/
theorem preimage_comparisonLiftOpen (g : A ⟶ B)
    (W : A.obj.thickening.target.scheme.Opens) :
    g.hom.targetHom.hom ⁻¹ᵁ comparisonLiftOpen g W = W := by
  have := A.property
  have hA := A.obj.thickening.isThickening
  have key : A.obj.thickening.immersion ⁻¹ᵁ (g.hom.targetHom.hom ⁻¹ᵁ comparisonLiftOpen g W) =
      A.obj.thickening.immersion ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, g.hom.immersion_naturality, Scheme.Hom.comp_preimage,
      comparisonLiftOpen, Stacks.Thickenings.IsThickening.preimage_opensCongr,
      ← Scheme.Hom.comp_preimage, g.hom.toX_naturality, Scheme.Hom.preimage_image_eq]
  rw [← hA.opensCongr_preimage (g.hom.targetHom.hom ⁻¹ᵁ comparisonLiftOpen g W), key,
    hA.opensCongr_preimage]

/-- **Over `comparisonLiftOpen` the two restrictions have the same underlying open of `X`.**  The
open underlying the restriction of the target is the image of a preimage along the open immersion
`U' ⟶ X`, hence the intersection of the open underlying the restriction of the source with the
image of `U'`, and that image contains the image of `U`. -/
theorem forgetToOpens_restrictOpen_comparisonLiftOpen (g : A ⟶ B)
    (W : A.obj.thickening.target.scheme.Opens) :
    (forgetToOpens S).obj
        (A.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ comparisonLiftOpen g W)) =
      (forgetToOpens S).obj (B.restrictOpen (comparisonLiftOpen g W)) := by
  have := A.property
  have := B.property
  rw [forgetToOpens_restrictOpen, forgetToOpens_restrictOpen, preimage_comparisonLiftOpen,
    comparisonLiftOpen, Stacks.Thickenings.IsThickening.preimage_opensCongr,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact (inf_eq_right.mpr
    ((Scheme.Hom.image_le_opensRange _ _).trans (leOfHom ((forgetToOpens S).map g)))).symm

variable (F : S.X.Modules)

/-- **The transition map of `F̲` over `comparisonLiftOpen` is invertible.**  The two restrictions
have the same underlying open of `X`, and `F̲` is `F` read on that open. -/
theorem isIso_map_restrictOpenMap_comparisonLiftOpen (g : A ⟶ B)
    (W : A.obj.thickening.target.scheme.Opens) :
    IsIso (F.val.presheaf.map
      ((forgetToOpens S).map (CrystallineThickening.restrictOpenMap g
        (comparisonLiftOpen g W))).op) := by
  have : IsIso ((forgetToOpens S).map (CrystallineThickening.restrictOpenMap g
      (comparisonLiftOpen g W))) :=
        ⟨homOfLE (forgetToOpens_restrictOpen_comparisonLiftOpen g W).ge, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩
  infer_instance

/-- **The comparison morphism `c_f : f^*(F̲)_{T'} ⟶ (F̲)_T` of `F̲` is surjective on sections over
every open of the ambient scheme**, for every morphism `f` of `Cris(X/S)`.

The image of `c_f` over the preimage of an open `W'` of `T'` contains the image of the transition
map `F̲(U' ∩ W', W', δ'|_{W'}) ⟶ F̲(U ∩ f^{-1}W', f^{-1}W', δ|_{f^{-1}W'})` of `F̲`, by
`PresheafOfModules.appₛₗ_mem_range_homEquivSymm_app`; and `comparisonLiftOpen` chooses, for a
given open `W` of `T`, an open `W'` of `T'` cutting out `W` for which that transition map is
invertible, because the two restrictions have the same underlying open of `X`. -/
theorem surjective_moduleComparison_app_underlineModules (g : A ⟶ B)
    (W : A.obj.thickening.target.scheme.Opens) :
    Function.Surjective
      ((CohomologyRestriction.moduleComparison (underlineModules S F).val g).app (op W)).hom := by
  have hsurj : Function.Surjective (((underlineModules S F).val.map
      (CrystallineThickening.restrictOpenMap g (comparisonLiftOpen g W)).op).hom) := by
    have := isIso_map_restrictOpenMap_comparisonLiftOpen F g W
    exact (ConcreteCategory.bijective_of_isIso (F.val.presheaf.map
      ((forgetToOpens S).map (CrystallineThickening.restrictOpenMap g
        (comparisonLiftOpen g W))).op)).surjective
  have main : Function.Surjective
      ((CohomologyRestriction.moduleComparison (underlineModules S F).val g).app
        (op (g.hom.targetHom.hom ⁻¹ᵁ comparisonLiftOpen g W))).hom := by
    intro y
    obtain ⟨z, hz⟩ := hsurj y
    obtain ⟨c, hc⟩ := PresheafOfModules.appₛₗ_mem_range_homEquivSymm_app
      (CohomologyRestriction.restrictionFMap (crisRing S) g)
      (CohomologyRestriction.moduleFMap (underlineModules S F).val g)
      (op (comparisonLiftOpen g W)) z
    exact ⟨c, hc.trans hz⟩
  exact preimage_comparisonLiftOpen g W ▸ main

end Comparison

/-- **Condition (2) of [Stacks, Tag 07JN] for `F̲`:** for every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` whose map on ambient schemes is a closed immersion,
the comparison morphism `c_f : f^*(F̲)_{T'} ⟶ (F̲)_T` is locally surjective on `T`.

It is in fact surjective on sections over every open of `T`, and for every morphism of
`Cris(X/S)`, the closed immersion hypothesis being unused:
`surjective_moduleComparison_app_underlineModules`. -/
theorem isSurjectiveComparison_underlineModules (F : S.X.Modules) :
    CohomologyRestriction.IsSurjectiveComparison (underlineModules S F).val := by
  intro A B g _hg
  exact Presheaf.isLocallySurjective_of_surjective _ _
    fun U ↦ surjective_moduleComparison_app_underlineModules F g U.unop

/-! ### Two lemmas on the sections of an open immersion -/

/-- Equal morphisms of schemes have equal maps on sections. -/
private theorem appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (U : Z.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- **Restriction along the open immersion of an open subscheme is inverse to the identification
of the global sections of that subscheme with the sections over the open.** -/
private theorem ι_appLE_comp_restrictFunctorΓ {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫
      (Scheme.restrictFunctorΓ (X := Y)).hom.app (op V) = 𝟙 _ := by
  rw [Scheme.Opens.ι_appLE, Scheme.restrictFunctorΓ_hom_app]
  exact (Y.presheaf.map_comp _ _).symm.trans
    ((congrArg Y.presheaf.map (Subsingleton.elim _ (𝟙 (op V)))).trans
      (Y.presheaf.map_id (op V)))

/-! ### The ring comparison, read through the open image -/

section Structure

variable (C : CrystallineThickening S)

/-- Every point of the thickened scheme of an object of `Cris(X/S)` lands in the open image of
that scheme in `X`. -/
theorem le_preimage_forgetToOpens :
    (⊤ : C.obj.thickening.source.Opens) ≤ C.obj.toX ⁻¹ᵁ ((forgetToOpens S).obj C) :=
  fun x _ ↦ ⟨x, rfl⟩

/-- **Restriction along the structure map `U ⟶ X` identifies the sections of `𝒪_X` over the open
image of `U` with the global sections of `U`**, that map being an open immersion onto that open
image. -/
instance isIso_toX_appLE_forgetToOpens :
    IsIso (C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤ (le_preimage_forgetToOpens C)) := by
  have := C.property
  have h : (⊤ : C.obj.thickening.source.Opens) = C.obj.toX ⁻¹ᵁ ((forgetToOpens S).obj C) :=
    le_antisymm (le_preimage_forgetToOpens C) le_top
  have : IsIso (homOfLE (le_preimage_forgetToOpens C)) :=
    ⟨homOfLE h.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : IsIso (C.obj.toX.app ((forgetToOpens S).obj C)) :=
    Scheme.Hom.isIso_app _ _ le_rfl
  rw [Scheme.Hom.appLE]
  infer_instance

/-- Restricting along the structure map of an object and then along the counit of
`opensFree ⊣ forgetToOpens` returns the sections of `𝒪_X` over the open image identically. -/
private theorem toX_appLE_comp_counit_appTop_comp_opensFreeStructureIso :
    (C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤ (le_preimage_forgetToOpens C) ≫
      ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom.appTop) ≫
      (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj C)) = 𝟙 _ := by
  have := C.property
  have h1 : ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom ≫ C.obj.toX =
      ((forgetToOpens S).obj C).ι :=
    ((opensFreeForgetAdjunction S).counit.app C).hom.toX_naturality
  have h7 := (congrArg (fun m ↦ C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤
      (le_preimage_forgetToOpens C) ≫ m)
    (Scheme.Hom.appLE_eq_app
      (f := ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom)
      (U := ⊤)).symm).trans
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _)
  refine ((congrArg (fun m ↦ m ≫ (opensFreeStructureIso S).hom.app
      (op ((forgetToOpens S).obj C))) h7).trans
    (congrArg (fun m ↦ m ≫ (opensFreeStructureIso S).hom.app
      (op ((forgetToOpens S).obj C)))
      (appLE_congr_hom h1 ((forgetToOpens S).obj C) _ _))).trans ?_
  exact ι_appLE_comp_restrictFunctorΓ ((forgetToOpens S).obj C)

/-- **The ring comparison `𝒪_{X/S} ⟶ G_a̲` of [Stacks, Tag 07IL], read through the open image.**
Composing its component at `(U, T, δ)` with the identification of `Γ(X, U)` with `Γ(U, 𝒪_U)`
leaves the map on global sections of the closed immersion `U ↪ T`.  Since that identification is
invertible, this pins the comparison down. -/
theorem structureToZariskiInverseImage_app_comp_appLE :
    (structureToZariskiInverseImage S).app (op C) ≫
        C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤ (le_preimage_forgetToOpens C) =
      C.obj.thickening.immersion.appTop := by
  have := C.property
  have h2 : ((opensFreeForgetAdjunction S).counit.app C).hom.targetHom.hom =
      ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom ≫
        C.obj.thickening.immersion :=
    (Category.id_comp _).symm.trans
      ((opensFreeForgetAdjunction S).counit.app C).hom.immersion_naturality
  have key2 : (((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom.appTop ≫
      (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj C))) ≫
      C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤ (le_preimage_forgetToOpens C) = 𝟙 _ := by
    have hinv : ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom.appTop ≫
        (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj C)) =
        inv (C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤ (le_preimage_forgetToOpens C)) := by
      rw [← cancel_epi (C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤
        (le_preimage_forgetToOpens C)), IsIso.hom_inv_id]
      exact (Category.assoc _ _ _).symm.trans
        (toX_appLE_comp_counit_appTop_comp_opensFreeStructureIso C)
    rw [hinv, IsIso.inv_hom_id]
  have h4 : (structureToZariskiInverseImage S).app (op C) =
      C.obj.thickening.immersion.appTop ≫
        ((opensFreeForgetAdjunction S).counit.app C).hom.sourceHom.appTop ≫
          (opensFreeStructureIso S).hom.app (op ((forgetToOpens S).obj C)) := by
    rw [structureToZariskiInverseImage_app_appTop]
    exact (congrArg (fun m ↦ m ≫ (opensFreeStructureIso S).hom.app
        (op ((forgetToOpens S).obj C)))
      ((congrArg Scheme.Hom.appTop h2).trans (Scheme.Hom.comp_appTop _ _))).trans
      (Category.assoc _ _ _)
  exact (congrArg (fun m ↦ m ≫ C.obj.toX.appLE ((forgetToOpens S).obj C) ⊤
      (le_preimage_forgetToOpens C)) h4).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ C.obj.thickening.immersion.appTop ≫ m) key2).trans
        (Category.comp_id _)))

end Structure

/-! ### The restriction of `F̲` to the ambient scheme of an object -/

/-- **Restriction to an open subscheme along its open immersion is the inverse of the
identification of its global sections with the sections over the open.** -/
private theorem ι_appLE_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens) (e : ⊤ ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  exact congrArg Y.presheaf.map (Subsingleton.elim _ _)

section Restriction

variable (A : CrystallineThickening S) (W : A.obj.thickening.target.scheme.Opens)

/-- **The ring comparison `𝒪_{X/S} ⟶ G_a̲` at a restriction `(U ∩ W, W, δ|_W)`, read on the
sections of the ambient scheme.**  Identifying `Γ(W, 𝒪_W)` with `Γ(T, W)` and the open of `X`
underlying the restriction with the image of the preimage of `W` in `U`, the comparison is the map
on sections over `W` of the closed immersion `U ↪ T` followed by the identification of the
sections of `𝒪_U` with the sections of `𝒪_X` over the image, `U ⟶ X` being an open immersion. -/
theorem structureToZariskiInverseImage_restrictOpen :
    (structureToZariskiInverseImage S).app (op (A.restrictOpen W)) ≫
        S.X.presheaf.map (eqToHom (forgetToOpens_restrictOpen A W).symm).op =
      W.topIso.hom ≫ A.obj.thickening.immersion.app W ≫
        (A.obj.toX.appIso (A.obj.thickening.immersion ⁻¹ᵁ W)).inv := by
  have := A.property
  set i := A.obj.thickening.immersion
  have e₂ : (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ (i ⁻¹ᵁ W).ι ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    (i ⁻¹ᵁ W).ι_preimage_self.ge
  have hs := structureToZariskiInverseImage_app_comp_appLE (A.restrictOpen W)
  have hle : i ⁻¹ᵁ W ≤ A.obj.toX ⁻¹ᵁ (forgetToOpens S).obj (A.restrictOpen W) := by
    rw [forgetToOpens_restrictOpen, Scheme.Hom.preimage_image_eq]
  have hsplit : A.obj.toX.appLE ((forgetToOpens S).obj (A.restrictOpen W)) (i ⁻¹ᵁ W) hle ≫
      (i ⁻¹ᵁ W).ι.appLE (i ⁻¹ᵁ W) ⊤ e₂ =
      (A.restrictOpen W).obj.toX.appLE ((forgetToOpens S).obj (A.restrictOpen W)) ⊤
        (le_preimage_forgetToOpens (A.restrictOpen W)) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hm : S.X.presheaf.map (eqToHom (forgetToOpens_restrictOpen A W).symm).op ≫
      (A.obj.toX.appIso (i ⁻¹ᵁ W)).hom ≫ (i ⁻¹ᵁ W).ι.appLE (i ⁻¹ᵁ W) ⊤ e₂ =
      A.obj.toX.appLE ((forgetToOpens S).obj (A.restrictOpen W)) (i ⁻¹ᵁ W) hle ≫
        (i ⁻¹ᵁ W).ι.appLE (i ⁻¹ᵁ W) ⊤ e₂ := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE_assoc]
  have hR : W.topIso.hom ≫ i.app W ≫ (i ⁻¹ᵁ W).ι.appLE (i ⁻¹ᵁ W) ⊤ e₂ = (i ∣_ W).appTop := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (morphismRestrict_ι i W).symm, ← Scheme.Hom.appLE_comp_appLE (i ∣_ W) W.ι W
        ⊤ ⊤ W.ι_preimage_self.ge le_rfl, ι_appLE_eq_topIso_inv, Iso.hom_inv_id_assoc]
    exact Scheme.Hom.appLE_eq_app _
  refine (cancel_mono ((A.obj.toX.appIso (i ⁻¹ᵁ W)).hom ≫
    (i ⁻¹ᵁ W).ι.appLE (i ⁻¹ᵁ W) ⊤ e₂)).1 ?_
  refine (Category.assoc _ _ _).trans (((congrArg
    ((structureToZariskiInverseImage S).app (op (A.restrictOpen W)) ≫ ·) (hm.trans hsplit)).trans
      hs).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hR.symm

/-- **The open of `X` underlying the restriction `(U ∩ W, W, δ|_W)`, as `W` varies**: it is the
image in `X` of the preimage of `W` in `U`, naturally in `W`. -/
def forgetToOpensRestrictOpenIso :
    CrystallineThickening.restrictOpenFunctor A ⋙ forgetToOpens S ≅
      Opens.map A.obj.thickening.immersion.base ⋙ A.obj.toX.opensFunctor :=
  NatIso.ofComponents (fun W ↦ eqToIso (forgetToOpens_restrictOpen A W))
    (fun _ ↦ Subsingleton.elim _ _)

variable (F : S.X.Modules)

/-- The abelian presheaf underlying the restriction of `F̲` to the ambient scheme of an object is
the one underlying the direct image along `U ↪ T` of the restriction of `F` to `U`. -/
def underlineRestrictionPresheafIso :
    (CrystallineThickening.restrictOpenFunctor A ⋙ forgetToOpens S).op ⋙ F.val.presheaf ≅
      (Opens.map A.obj.thickening.immersion.base ⋙ A.obj.toX.opensFunctor).op ⋙
        F.val.presheaf :=
  Functor.isoWhiskerRight (NatIso.op (forgetToOpensRestrictOpenIso A)).symm F.val.presheaf

/-- **The restriction of `F̲` to the ambient scheme `T` of an object `(U, T, δ)` is the direct
image along the closed immersion `U ↪ T` of the restriction of `F` to the open `U` of `X`**, as
sheaves of modules over the restriction of `𝒪_{X/S}` to `T`.  On sections over an open `W` of `T`
both are `F` over the image in `X` of the preimage of `W` in `U`; that the two module structures
agree is `structureToZariskiInverseImage_restrictOpen`. -/
def underlineRestrictionIso :
    CohomologyRestriction.moduleRestrictionSheaf (underlineModules S F) A ≅
      (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A.obj).hom).obj
        ((Scheme.Modules.pushforward A.obj.thickening.immersion).obj
          (F.restrict A.obj.toX)) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    { hom := PresheafOfModules.homMk (underlineRestrictionPresheafIso A F).hom ?_
      inv := PresheafOfModules.homMk (underlineRestrictionPresheafIso A F).inv ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro W r m
    have key := congrArg (fun φ ↦ φ.hom r) (structureToZariskiInverseImage_restrictOpen A W.unop)
    exact (F.val.map_smul _ _ m).trans (congrArg (· • _) key)
  · intro W r m
    have key := congrArg (fun φ ↦ φ.hom r) (structureToZariskiInverseImage_restrictOpen A W.unop)
    have hid : ((structureToZariskiInverseImage S).app (op (A.restrictOpen W.unop)) ≫
        S.X.presheaf.map (eqToHom (forgetToOpens_restrictOpen A W.unop).symm).op) ≫
        S.X.presheaf.map ((NatIso.op (forgetToOpensRestrictOpenIso A)).symm.inv.app W) =
        (structureToZariskiInverseImage S).app (op (A.restrictOpen W.unop)) :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        ((S.X.presheaf.map_comp _ _).symm.trans ((congrArg S.X.presheaf.map
          (Subsingleton.elim _ _)).trans (S.X.presheaf.map_id _)))).trans (Category.comp_id _))
    refine (F.val.map_smul _ _ m).trans (congrArg (· • _) ?_)
    exact (congrArg (S.X.presheaf.map
      ((NatIso.op (forgetToOpensRestrictOpenIso A)).symm.inv.app W)).hom key.symm).trans
        (congrArg (fun φ ↦ φ.hom r) hid)
  · ext W m
    exact ConcreteCategory.congr_hom ((underlineRestrictionPresheafIso A F).hom_inv_id_app W) m
  · ext W m
    exact ConcreteCategory.congr_hom ((underlineRestrictionPresheafIso A F).inv_hom_id_app W) m

end Restriction

/-! ### Condition (1) of [Stacks, Tag 07JN] for `F̲` -/

/-- **Condition (1) of [Stacks, Tag 07JN] for `F̲`: for a quasi-coherent `𝒪_X`-module `F`, the
sheaf `F̲` on `Cris(X/S)` is locally quasi-coherent.**  Its restriction to the ambient scheme `T`
of an object `(U, T, δ)` is the direct image along the closed immersion `U ↪ T` of the
restriction of `F` to the open `U` of `X` (`underlineRestrictionIso`); the restriction of a
quasi-coherent module to an open is quasi-coherent, and so is its direct image along a closed
immersion, a closed immersion being affine ([Stacks, Tag 01XJ]). -/
theorem isLocallyQuasiCoherent_underlineModules (F : S.X.Modules) [F.IsQuasicoherent] :
    IsLocallyQuasiCoherent (underlineModules S F) := by
  intro A
  refine ⟨(CohomologyRestriction.moduleRestrictionSheaf (underlineModules S F) A).isSheaf, ?_⟩
  have := A.obj.thickening.isThickening.1
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso (underlineRestrictionIso A F).symm
    (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ _
      (SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent
        ((Scheme.Modules.pushforward A.obj.thickening.immersion).obj (F.restrict A.obj.toX))))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
