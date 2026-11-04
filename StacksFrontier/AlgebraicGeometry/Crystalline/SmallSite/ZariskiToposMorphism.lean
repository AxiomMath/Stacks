module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ForgetToZariski
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The crystalline-to-Zariski morphism of topoi

Fix a global crystalline situation `(p, (S, I, γ), X)`.  Forgetting the divided power thickening
of an object of the small crystalline site is a functor `Cris(X/S) ⥤ X_Zar`, `(U, T, δ) ↦ U`,
[Stacks, Tag 07IH].  This file establishes the four properties of that functor asserted by
[Stacks, Tag 07IL] and constructs the morphism of topoi they give.

The small Zariski site `X_Zar` is read here as the lattice `X.Opens` of open subsets of `X` with
its usual topology `Opens.grothendieckTopology`, so that the small Zariski topos `Sh(X_Zar)` is
the topos of sheaves of sets on the topological space `X`; the functor is
`Crystalline.GlobalCrystallineSituation.forgetToOpens`, which sends `(U, T, δ)` to the open image
of `U ⟶ X`.  That this is the same functor as the one into the small Zariski site inside a chosen
big Zariski site is the identity
`Crystalline.GlobalCrystallineSituation.forgetToZariski_comp_smallZariskiToOpens`, whose second
factor `AlgebraicGeometry.smallZariskiToOpens` is an equivalence of sites
(`AlgebraicGeometry.smallZariskiToOpens_isEquivalence`, [Stacks, Tag 020X]), so the two readings
have the same topos.

The engine for three of the four properties is an adjunction.  An open `V` of `X` is the thickened
scheme of the object `(V, V, ∅)` of `Cris(X/S)` whose ambient scheme carries the zero divided power
ideal, and a morphism `(V, V, ∅) ⟶ (U, T, δ)` is exactly an inclusion `V ⊆ U` of opens of `X`:
its map on thickened schemes is the unique `X`-morphism `V ⟶ U` and its divided power map is forced
to be `V ⟶ U ↪ T`, which is a divided power morphism because the immersion `U ↪ T` kills the
divided power ideal of `T`.  So `V ↦ (V, V, ∅)` is left adjoint to the forgetful functor, which is
therefore representably flat and preserves every limit that exists — in particular products and
fibred products.

Cocontinuity is the argument of [Stacks, Tag 07ID] carried out on the small sites: a covering of
the open `U` of `X` pulls back to a covering of the thickened scheme of `(U, T, δ)`, and the
immersion `U ↪ T` is a thickening, hence a homeomorphism on points, so that covering is the
restriction of a covering of the ambient scheme `T`; the corresponding restrictions of `(U, T, δ)`
form a Zariski covering family refining the given one.  Continuity is the reverse: the thickened
schemes of a Zariski covering family cover, because the ambient schemes do and the immersion is a
homeomorphism.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.opensFree` — the functor `X_Zar ⥤ Cris(X/S)`,
  `V ↦ (V, V, ∅)`.
* `Crystalline.GlobalCrystallineSituation.opensFreeForgetAdjunction` — it is left adjoint to the
  forgetful functor of [Stacks, Tag 07IH].
* `Crystalline.GlobalCrystallineSituation.zariskiToposMorphism` — the morphism of topoi
  `u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` of [Stacks, Tag 07IL].

## Main results

* `Crystalline.GlobalCrystallineSituation.forgetToOpens_zariskiCovering_functorPushforward_mem` —
  the functor is continuous: the image of a Zariski covering family of `Cris(X/S)` is a covering
  of the small Zariski site, [Stacks, Tag 07IL].
* `Crystalline.GlobalCrystallineSituation.forgetToOpens_isCocontinuous` — the functor is
  cocontinuous, [Stacks, Tag 07IL].
* `Crystalline.GlobalCrystallineSituation.forgetToOpens_preservesBinaryProducts` and
  `Crystalline.GlobalCrystallineSituation.forgetToOpens_preservesPullbacks` — the functor commutes
  with products and with fibred products, [Stacks, Tag 07IL].

## Implementation notes

Continuity in the sense of [Stacks, Tag 00WV] is the conjunction of
`forgetToOpens_zariskiCovering_functorPushforward_mem` (covering families go to covering families)
and `forgetToOpens_preservesPullbacks` (compatibility with the fibre products involved), the
second of which is a clause of [Stacks, Tag 07IL] in its own right.  Mathlib's
`CategoryTheory.Functor.IsContinuous` — the sheaf-theoretic form of [Stacks, Tag 00WW] — is not
claimed: the only route to it from cover preservation, `coverPreserving_of_generators`, requires
the source site to have pullbacks, and neither `Cris(X/S)` nor `CRIS(X/S)` has them in this
library.  The existence half of [Stacks, Tag 07I9] is not carried — only its second assertion is,
as `Crystalline.GlobalCrystallineSituation.forget_preservesLimits` — and constructing those limits
needs divided power envelopes.

The morphism of topoi is obtained from cocontinuity alone, as in [Stacks, Tag 00XO]: its
pushforward is `{}_s u` and its inverse image the left adjoint `(u^p\ )^#` of
`CategoryTheory.Functor.sheafPullbackCocontinuous`, which is left exact by [Stacks, Tag 00XL].
Section 7.21 of the Sites chapter, [Stacks, Tag 00XN], is not carried as such; what is used of it
is `CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous` and
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullbackCocontinuous` together with
`MorphismOfTopoi`, the library's rendering of [Stacks, Tag 00XA].

## References

* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07ID](https://stacks.math.columbia.edu/tag/07ID)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe w w' u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **An open of `X`, viewed as the object `(V, V, ∅)` of the small crystalline site.**  The
scheme `V` is thickened by itself, the ambient scheme carrying the zero divided power ideal, and
its structure map to `X` is the open immersion of `V`.  This is the composite of the open
subscheme functor of `X` with the trivial thickening of [Stacks, Tag 07I8]. -/
def opensFree (S : GlobalCrystallineSituation.{u}) : S.X.Opens ⥤ CrystallineThickening S :=
  (Thickening.IsCrystalline (S := S)).lift (S.X.restrictFunctor ⋙ free S)
    fun V ↦ inferInstanceAs (IsOpenImmersion V.ι)

/-- The underlying thickening of `opensFree S` at `V` is the trivial thickening of `V ⟶ X`. -/
@[simp]
theorem opensFree_obj_obj (V : S.X.Opens) :
    ((opensFree S).obj V).obj = (free S).obj (Over.mk V.ι) := rfl

/-- The thickened scheme of `opensFree S` at `V` is `V`. -/
@[simp]
theorem opensFree_obj_source (V : S.X.Opens) :
    ((opensFree S).obj V).obj.thickening.source = V.toScheme := rfl

/-- The structure map to `X` of `opensFree S` at `V` is the open immersion `V.ι`. -/
@[simp]
theorem opensFree_obj_toX (V : S.X.Opens) : ((opensFree S).obj V).obj.toX = V.ι := rfl

/-- **A morphism out of `(V, V, ∅)` is unique.**  Its map on thickened schemes is a morphism over
`X` into an open subscheme of `X`, hence determined, and its divided power map on ambient schemes
is then forced by the compatibility with the immersions, the immersion of `(V, V, ∅)` being the
identity. -/
theorem opensFree_hom_ext {V : S.X.Opens} {A : CrystallineThickening S}
    (f g : (opensFree S).obj V ⟶ A) : f = g := by
  have hs : f.hom.sourceHom = g.hom.sourceHom :=
    (cancel_mono A.obj.toX).1 (by rw [f.hom.toX_naturality, g.hom.toX_naturality])
  refine ObjectProperty.hom_ext _ (Thickening.Hom.ext hs (DividedPowerScheme.Hom.ext ?_))
  have h (k : (opensFree S).obj V ⟶ A) :
      k.hom.targetHom.hom = k.hom.sourceHom ≫ A.obj.thickening.immersion :=
    (Category.id_comp _).symm.trans k.hom.immersion_naturality
  rw [h f, h g, hs]

/-- **The open of `X` underlying a morphism out of `(V, V, ∅)` contains `V`.**  The map on
thickened schemes of such a morphism is a morphism over `X` out of `V`. -/
theorem le_opensRange_toX_of_opensFree_hom {V : S.X.Opens} {A : CrystallineThickening S}
    (f : (opensFree S).obj V ⟶ A) : V ≤ A.obj.toX.opensRange := by
  have h : Set.range ((opensFree S).obj V).obj.toX.base ⊆ Set.range A.obj.toX.base := by
    rw [← f.hom.toX_naturality]
    rintro _ ⟨x, rfl⟩
    exact ⟨f.hom.sourceHom x, (Scheme.Hom.comp_apply _ _ x).symm⟩
  exact fun x hx ↦ h ((Scheme.Opens.range_ι V).ge hx)

/-- **The unique `X`-morphism from an open `V` of `X` contained in the open image of the thickened
scheme of an object of `Cris(X/S)` to that thickened scheme.** -/
def opensLiftToX {V : S.X.Opens} {A : CrystallineThickening S} (h : V ≤ A.obj.toX.opensRange) :
    V.toScheme ⟶ A.obj.thickening.source :=
  IsOpenImmersion.lift A.obj.toX V.ι fun _ hx ↦ h ((Scheme.Opens.range_ι V).le hx)

/-- The morphism `opensLiftToX h` composed with the structure map to `X` is `V.ι`. -/
@[simp]
theorem opensLiftToX_comp_toX {V : S.X.Opens} {A : CrystallineThickening S}
    (h : V ≤ A.obj.toX.opensRange) : opensLiftToX h ≫ A.obj.toX = V.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- **Stacks Project, Tag 07II for the small Zariski site read in the opens of `X`.**  The functor
`V ↦ (V, V, ∅)` is left adjoint to the forgetful functor of [Stacks, Tag 07IH]: a morphism
`(V, V, ∅) ⟶ (U, T, δ)` of the small crystalline site is exactly an inclusion `V ⊆ U` of opens of
`X`. -/
def opensFreeForgetAdjunction (S : GlobalCrystallineSituation.{u}) :
    opensFree S ⊣ forgetToOpens S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V A ↦
        { toFun := fun f ↦ homOfLE (le_opensRange_toX_of_opensFree_hom f)
          invFun := fun h ↦ ObjectProperty.homMk
            (((freeForgetAdjunction S).homEquiv (Over.mk V.ι) A.obj).symm
              (Over.homMk (opensLiftToX (leOfHom h)) (opensLiftToX_comp_toX (leOfHom h))))
          left_inv := fun _ ↦ opensFree_hom_ext _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm := fun _ _ ↦ opensFree_hom_ext _ _
      homEquiv_naturality_right := fun _ _ ↦ Subsingleton.elim _ _ }

/-- The forgetful functor of [Stacks, Tag 07IH] is a right adjoint. -/
instance forgetToOpens_isRightAdjoint (S : GlobalCrystallineSituation.{u}) :
    (forgetToOpens S).IsRightAdjoint :=
  (opensFreeForgetAdjunction S).isRightAdjoint

/-- **The forgetful functor of [Stacks, Tag 07IH] commutes with every limit that exists**, being a
right adjoint. -/
instance forgetToOpens_preservesLimitsOfSize (S : GlobalCrystallineSituation.{u}) :
    PreservesLimitsOfSize.{w, w'} (forgetToOpens S) :=
  (opensFreeForgetAdjunction S).rightAdjoint_preservesLimits

/-- **Stacks Project, Tag 07IL.**  The forgetful functor `Cris(X/S) ⥤ X_Zar` of
[Stacks, Tag 07IH] commutes with products. -/
@[stacks 07IL "the functor (07IH) commutes with products"]
instance forgetToOpens_preservesBinaryProducts (S : GlobalCrystallineSituation.{u}) :
    PreservesLimitsOfShape (Discrete WalkingPair) (forgetToOpens S) :=
  inferInstance

/-- **Stacks Project, Tag 07IL.**  The forgetful functor `Cris(X/S) ⥤ X_Zar` of
[Stacks, Tag 07IH] commutes with fibred products. -/
@[stacks 07IL "the functor (07IH) commutes with fibred products"]
instance forgetToOpens_preservesPullbacks (S : GlobalCrystallineSituation.{u}) :
    PreservesLimitsOfShape WalkingCospan (forgetToOpens S) :=
  inferInstance

/-- **The thickened schemes of a Zariski covering family of `Cris(X/S)` cover.**  The ambient
divided power schemes cover the ambient scheme of the base, each square is Cartesian, and the
immersion of the base is a thickening, hence surjective; so a point of the thickened scheme of the
base lifts to the member whose ambient scheme covers its image. -/
theorem Thickening.exists_mem_range_sourceHom {A : Thickening S}
    (E : PreZeroHypercover.{u + 1} A) (hE : Thickening.IsZariskiCovering E)
    (y : A.thickening.source) :
    ∃ i, y ∈ Set.range (E.f i).sourceHom.base := by
  obtain ⟨hcart, hcov⟩ := hE
  simp only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] at hcov
  obtain ⟨hsurj, hoi⟩ := hcov
  obtain ⟨i, t, ht⟩ := hsurj (A.thickening.immersion.base y)
  have : IsOpenImmersion (E.f i).targetHom.hom := hoi i
  obtain ⟨z, hz⟩ : y ∈ Set.range (pullback.fst A.thickening.immersion
      (E.f i).targetHom.hom).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact ⟨t, ht⟩
  refine ⟨i, (hcart i).isoPullback.inv.base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, (hcart i).isoPullback_inv_fst, hz]

/-- **The thickened schemes of a Zariski covering family of `Cris(X/S)` cover.**  The covering
notion of the small crystalline site is the one of the big site, taken on the image of the family
under the inclusion `Cris(X/S) ⥤ CRIS(X/S)`. -/
theorem CrystallineThickening.exists_mem_range_sourceHom {A : CrystallineThickening S}
    (E : PreZeroHypercover.{u + 1} A) (hE : CrystallineThickening.IsZariskiCovering E)
    (y : A.obj.thickening.source) :
    ∃ i, y ∈ Set.range (E.f i).hom.sourceHom.base :=
  Thickening.exists_mem_range_sourceHom (E.map (CrystallineThickening.ι S)) hE y

/-- **Stacks Project, Tag 07IL.**  The forgetful functor `Cris(X/S) ⥤ X_Zar` of
[Stacks, Tag 07IH] is continuous: the image of a Zariski covering family of the small crystalline
site is a covering of the small Zariski site of `X`. -/
@[stacks 07IL "the functor (07IH) is continuous: it carries covering families to coverings"]
theorem forgetToOpens_zariskiCovering_functorPushforward_mem
    (S : GlobalCrystallineSituation.{u}) {A : CrystallineThickening S}
    (E : PreZeroHypercover.{u + 1} A) (hE : CrystallineThickening.IsZariskiCovering E) :
    E.sieve₀.functorPushforward (forgetToOpens S) ∈
      Opens.grothendieckTopology S.X.carrier ((forgetToOpens S).obj A) := by
  rw [← PreZeroHypercover.sieve₀_map, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range A.obj.toX.base := hx
  obtain ⟨i, z, hz⟩ := CrystallineThickening.exists_mem_range_sourceHom E hE y
  exact ⟨(forgetToOpens S).obj (E.X i), (forgetToOpens S).map (E.f i),
    Sieve.le_generate (E.map (forgetToOpens S)).presieve₀ _ _ (Presieve.ofArrows.mk i),
    ⟨z, by rw [← (E.f i).hom.toX_naturality, Scheme.Hom.comp_apply, hz]⟩⟩

/-- **The restriction of an object of `Cris(X/S)` to an open of its ambient scheme lies over any
open of `X` with the same preimage in the thickened scheme.** -/
private theorem forgetToOpens_obj_restrictOpen_le {A : CrystallineThickening S}
    {V : A.obj.thickening.target.scheme.Opens} {W : S.X.Opens}
    (h : A.obj.thickening.immersion ⁻¹ᵁ V = A.obj.toX ⁻¹ᵁ W) :
    (forgetToOpens S).obj (A.restrictOpen V) ≤ W := by
  intro x hx
  obtain ⟨c, rfl⟩ : x ∈ Set.range (A.restrictOpen V).obj.toX.base := hx
  change _ ∈ A.obj.toX ⁻¹ᵁ W
  rw [← h]
  exact (Scheme.Opens.range_ι _).le (Set.mem_range_self c)

/-- **Stacks Project, Tag 07IL.**  The forgetful functor `Cris(X/S) ⥤ X_Zar` of
[Stacks, Tag 07IH] is cocontinuous.  A covering sieve of the open `U` of `X` underlying an object
`(U, T, δ)` of `Cris(X/S)` gives, for every point of `T`, an open of `X` in the sieve containing
the image of that point; the preimages in `U` of those opens match opens of `T`, because the
immersion `U ↪ T` is a thickening and therefore a homeomorphism on points, and the restrictions of
`(U, T, δ)` to them form a Zariski covering family of `Cris(X/S)` each of whose members lands in
the sieve. -/
@[stacks 07IL "the functor (07IH) is cocontinuous"]
instance forgetToOpens_isCocontinuous (S : GlobalCrystallineSituation.{u}) :
    (forgetToOpens S).IsCocontinuous (smallTopology S)
      (Opens.grothendieckTopology S.X.carrier) := by
  classical
  refine ⟨fun {A T} hT ↦ ?_⟩
  rw [Opens.mem_grothendieckTopology] at hT
  have hi : Stacks.Thickenings.IsThickening A.obj.thickening.immersion :=
    A.obj.thickening.isThickening
  choose W g hg hmem using fun i : ULift.{u + 1, u} A.obj.thickening.target.scheme ↦
    hT (A.obj.toX.base (hi.homeomorph.symm i.down)) ⟨hi.homeomorph.symm i.down, rfl⟩
  set V : ULift.{u + 1, u} A.obj.thickening.target.scheme →
      A.obj.thickening.target.scheme.Opens :=
    fun i ↦ hi.opensCongr (A.obj.toX ⁻¹ᵁ W i)
  have hpre (i : ULift.{u + 1, u} A.obj.thickening.target.scheme) :
      A.obj.thickening.immersion ⁻¹ᵁ V i = A.obj.toX ⁻¹ᵁ W i :=
    hi.preimage_opensCongr _
  have himm (t : A.obj.thickening.target.scheme) :
      A.obj.thickening.immersion.base (hi.homeomorph.symm t) = t :=
    hi.homeomorph.apply_symm_apply t
  have hcov (t : A.obj.thickening.target.scheme) : ∃ i, t ∈ V i := by
    refine ⟨ULift.up t, ?_⟩
    have h1 : A.obj.thickening.immersion.base (hi.homeomorph.symm t) ∈ V (ULift.up t) := by
      change hi.homeomorph.symm t ∈ A.obj.thickening.immersion ⁻¹ᵁ V (ULift.up t)
      rw [hpre]
      exact hmem (ULift.up t)
    rwa [himm t] at h1
  refine (smallTopology S).superset_covering ?_
    (smallZariskiCovering_mem_smallTopology S (A.restrictOpenCover V)
      (CrystallineThickening.isZariskiCovering_restrictOpenCover A V hcov))
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  change T.arrows ((forgetToOpens S).map (A.restrictOpenHom (V i)))
  have hle := forgetToOpens_obj_restrictOpen_le (hpre i)
  have hsub := T.downward_closed (hg i) (homOfLE hle)
  rwa [Subsingleton.elim (homOfLE hle ≫ g i)
    ((forgetToOpens S).map (A.restrictOpenHom (V i)))] at hsub

/-- **Stacks Project, Tag 07IL.**  The morphism of topoi
`u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` relating the small crystalline topos of `X/S` with the small
Zariski topos of `X`, induced by the cocontinuous forgetful functor `Cris(X/S) ⥤ X_Zar` of
[Stacks, Tag 07IH].  Its pushforward is the sheaf pushforward along that functor and its inverse
image the sheaf pullback, which is left exact. -/
@[stacks 07IL "the morphism of topoi u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)",
  sga "4 III 2.3" "special case"]
def zariskiToposMorphism (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (smallTopos S)
      (Sheaf (Opens.grothendieckTopology S.X.carrier) (Type (u + 1))) where
  pushforward := (forgetToOpens S).sheafPushforwardCocontinuous (Type (u + 1))
    (smallTopology S) (Opens.grothendieckTopology S.X.carrier)
  inverseImage := (forgetToOpens S).sheafPullbackCocontinuous (Type (u + 1))
    (smallTopology S) (Opens.grothendieckTopology S.X.carrier)
  adj := (forgetToOpens S).sheafAdjunctionPullbackCocontinuous (Type (u + 1))
    (smallTopology S) (Opens.grothendieckTopology S.X.carrier)
  preservesFiniteLimits := inferInstance

end Crystalline.GlobalCrystallineSituation

end
