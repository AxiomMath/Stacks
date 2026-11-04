module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningKernel

/-!
# The second-order universal thickening as an object of the crystalline site

Let `(U, T, δ)` be an object of the big crystalline category `CRIS(X/S)` of a global crystalline
situation.  `StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickening.lean` builds the
structure sheaf `𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` of the second-order
universal thickening of `T`, its ideal `J''`, its divided power structure `δ''`, and five of the
six maps `q₀, q₁, q₂, q₀₁, q₀₂` of [Stacks, Tag 07J3]; the sixth, `q₁₂`, is built in
`SecondOrderThickeningDeRham.lean`.  All of that is a construction with *sheaves* of rings.  This
module turns it into geometry: `T''` is realized as a scheme, as a divided power scheme carrying
`δ''`, and as an object of `CRIS(X/S)` and of `Cris(X/S)`, sitting in the diagram

```
  T''  ⇛  T'  ⇉  T
```

of the site — three morphisms `q₀, q₁, q₂ : T'' ⟶ T`, three morphisms
`q₀₁, q₁₂, q₀₂ : T'' ⟶ T'`, and the six relations
`q₀ = q₀₁ ∘ p₀`, `q₁ = q₀₁ ∘ p₁`, `q₁ = q₁₂ ∘ p₀`, `q₂ = q₁₂ ∘ p₁`, `q₀ = q₀₂ ∘ p₀`,
`q₂ = q₀₂ ∘ p₁` between them.

## Main definitions

* `Crystalline.secondOrderThickeningExtension` — the square-zero extension of `𝒪_{T'}` by
  `K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`, in the sense of
  `Stacks.Thickenings.SquareZeroExtension`.
* `Crystalline.secondOrderThickeningScheme` — the scheme `T''`, with structure sheaf `𝒪_{T''}` on
  the topological space of `T`.
* `Crystalline.secondOrderThickeningι` and `Crystalline.secondOrderThickeningιT` — the immersions
  `T' ⟶ T''` and `T ⟶ T''`.
* `Crystalline.secondOrderThickeningQ₀₁Hom`, `Crystalline.secondOrderThickeningQ₁₂Hom`,
  `Crystalline.secondOrderThickeningQ₀₂Hom` — the morphisms of schemes `T'' ⟶ T'`, and
  `Crystalline.secondOrderThickeningQ₀Hom`, `Crystalline.secondOrderThickeningQ₁Hom`,
  `Crystalline.secondOrderThickeningQ₂Hom` — the morphisms of schemes `T'' ⟶ T`.
* `Crystalline.GlobalCrystallineSituation.secondOrderThickeningDPScheme` — the divided power
  scheme `(T'', J'', δ'')`.
* `Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject` — the object
  `(U, T'', δ'')` of `CRIS(X/S)`, with the six morphisms
  `Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₀` and its siblings.
* `Crystalline.GlobalCrystallineSituation.secondOrderThickeningCrysObject` — the same object in
  the small crystalline category `Cris(X/S)`, with its six morphisms.

## Main results

* `Crystalline.secondOrderThickeningScheme_obj` — the sections of the structure sheaf of `T''`
  are the sections of `𝒪_{T''}`.
* `Crystalline.secondOrderThickeningι_isFirstOrderThickening` — `T' ⟶ T''` is a first-order
  thickening of schemes.
* `Crystalline.secondOrderThickeningιT_isNthOrderThickening` — **`T → T''` is a second-order
  thickening of schemes**, the description of `T''` that [Stacks, Tag 07J3] gives.
* `Crystalline.secondOrderThickeningQ₀Hom_eq_Q₀₁_comp_P₀` and its five siblings — the six
  composition relations, for schemes; `…SiteQ₀₁_comp_P₀` and its siblings are the same relations
  in `CRIS(X/S)`, and `…CrysQ₀₁_comp_P₀` and its siblings in `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.secondOrderThickeningIdealSheaf_isQuasicoherent` — the
  ideal `J''` is quasi-coherent, being the ideal sheaf of the closed immersion `U ⟶ T''`.

## Implementation notes

`Stacks.Thickenings.squareZeroExtension_realization` [Stacks, Tag 05YV] realizes a square-zero
extension of a structure sheaf as a scheme, and its `square_zero` field is a *literal* vanishing
of the square of the kernel.  As
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder` shows
(`Crystalline.secondOrderThickening_ker_sq_eq_bot_iff`), the ideal of `T → T''` has that property
only when every exterior product of divided power differentials vanishes, so the realization
theorem cannot be applied to `𝒪_{T''} → 𝒪_T`.  `T''` is therefore realized over the *first-order*
thickening `T'` instead, in a single square-zero step with kernel
`K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`
(`Crystalline.secondOrderThickening_ker_proj_sq`), whose quasi-coherence is
`Crystalline.secondOrderKerSheaf_isQuasicoherent`.  As in the first-order case, the realization
is used only to transport the two properties of the space of `T` carrying `𝒪_{T''}` that are not
immediate — that its stalks are local rings and that it is locally affine — so every statement
about sections of `𝒪_{T''}` below holds with no transport, and the opens of `T''` are the opens of
`T`.

The three morphisms `q₀, q₁, q₂ : T'' ⟶ T` are *defined* as the composites `q₀₁ ∘ p₀`,
`q₀₁ ∘ p₁` and `q₁₂ ∘ p₁`, which makes three of the six relations hold by definition.  The other
three are proved from their sheaf-level counterparts through
`Crystalline.secondOrderThickeningHomT_ext`, which compares the two morphisms by way of the
*small* sheafed-space data they are built from rather than directly: a direct comparison of two
morphisms of this size is not tractable, because the kernel attempts a congruence on the two
underlying morphisms of schemes before unfolding them.  The same device is
`Crystalline.firstOrderThickeningHomFromT_ext`, used for the three retractions
`q₀₁ ∘ (T ⟶ T'') = q₀₂ ∘ (T ⟶ T'') = q₁₂ ∘ (T ⟶ T'') = (T ⟶ T')`.

## What is and is not proved

**The order of the thickening `T → T''` is not deduced from the two first-order steps.**  A
composite of two first-order thickenings of schemes is in general only of order *three*: for
`Z = Spec k[x]/(x⁴)` the closed subschemes cut out by `(x²)` and by `(x)` give first-order
thickenings whose composite has `(x)³ ≠ 0`.  What makes the order two here is the explicit
vanishing of the cube of the ideal of `𝒪_{T''} → 𝒪_T`,
`Crystalline.secondOrderThickening_ker_cube`, transported to the scheme level in
`Crystalline.secondOrderThickeningιT_isNthOrderThickening`.

`δ''` is the divided power structure of the remark,
`Crystalline.secondOrderThickeningDividedPowers` —
`Crystalline.secondOrderThickeningDividedPowers_dpow_add_two` is its displayed formula — and
the compatibility of each of the six maps with the divided powers is the corresponding
lemma of `SecondOrderThickening.lean` and `SecondOrderThickeningDeRham.lean`, used as the
`compatible` field of the six morphisms of divided power schemes.  Nothing weaker is recorded
under Tag 07J3.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 07I4](https://stacks.math.columbia.edu/tag/07I4)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### The square-zero extension datum over `T'` -/

/-- The inclusion of the kernel `K` into the sections of `𝒪_{T''}` as the square-zero ideal of
`T' → T''`: a pair `(ω, η)` is the section `(0, 0, ω, η)`. -/
public def secondOrderThickeningInr (W : (Opens ↑T.scheme)ᵒᵖ) :
    SecondOrderKer T Y f W →+ SecondOrderExt (dpWedge T Y f) W where
  toFun x := secondOrderExtMk 0 0 (secondOrderKerFst x) (secondOrderKerSnd x)
  map_zero' := rfl
  map_add' _ _ := secondOrderExt_ext (add_zero (0 : _)).symm (add_zero (0 : _)).symm rfl rfl

/-- The first coordinate of the section `(0, 0, ω, η)` is zero. -/
@[simp] public theorem secondOrderExtFst_inr (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderKer T Y f W) :
    secondOrderExtFst (secondOrderThickeningInr T Y f W x) = 0 := rfl

/-- The first middle coordinate of the section `(0, 0, ω, η)` is zero. -/
@[simp] public theorem secondOrderExtLeft_inr (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderKer T Y f W) :
    secondOrderExtLeft (secondOrderThickeningInr T Y f W x) = 0 := rfl

/-- The second middle coordinate of the section `(0, 0, ω, η)` is `ω`. -/
@[simp] public theorem secondOrderExtRight_inr (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderKer T Y f W) :
    secondOrderExtRight (secondOrderThickeningInr T Y f W x) = secondOrderKerFst x := rfl

/-- The top coordinate of the section `(0, 0, ω, η)` is `η`. -/
@[simp] public theorem secondOrderExtTop_inr (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderKer T Y f W) :
    secondOrderExtTop (secondOrderThickeningInr T Y f W x) = secondOrderKerSnd x := rfl

/-- **Multiplying a section of the ideal of `T' → T''` by an arbitrary section of `𝒪_{T''}` acts
on the kernel by the twisted scalar multiplication**: this identifies the `𝒪_{T'}`-module
structure of `K` with multiplication inside `𝒪_{T''}`, and it is where the exterior-product
twist of `Crystalline.SecondOrderKer` comes from. -/
public theorem secondOrderThickeningInr_smul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : SecondOrderExt (dpWedge T Y f) W) (x : SecondOrderKer T Y f W) :
    secondOrderThickeningInr T Y f W
        (((secondOrderThickeningProj T Y f).app W).hom a • x) =
      a * secondOrderThickeningInr T Y f W x := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_
  · rw [secondOrderExtFst_inr, secondOrderExtFst_mul, secondOrderExtFst_inr, mul_zero]
  · rw [secondOrderExtLeft_inr, secondOrderExtLeft_mul, secondOrderExtLeft_inr,
      secondOrderExtFst_inr, smul_zero, zero_smul, add_zero]
  · rw [secondOrderExtRight_inr, secondOrderExtRight_mul, secondOrderExtRight_inr,
      secondOrderExtFst_inr, zero_smul, add_zero, secondOrderKerFst_smul,
      secondOrderThickeningProj_fst]
  · rw [secondOrderExtTop_inr, secondOrderExtTop_mul, secondOrderExtTop_inr,
      secondOrderExtFst_inr, secondOrderExtLeft_inr, secondOrderExtRight_inr, zero_smul,
      bilinearApp_zero_left, add_zero, add_zero, secondOrderKerSnd_smul,
      secondOrderThickeningProj_fst, secondOrderThickeningProj_snd]

/-- **The square-zero extension of `𝒪_{T'}` by `K`.**  The structure sheaf `𝒪_{T''}` of the
second-order universal thickening, its projection onto `𝒪_{T'}` and the quasi-coherent kernel
`K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` of that projection, packaged as the input of the
realization theorem [Stacks, Tag 05YV].  The base is `T'` itself, with `q₀₁` as the structure
map; `q₀₁` splits the projection, which is the relation `q₀₁ ∘ (T' ⟶ T'') = id`. -/
public def secondOrderThickeningExtension :
    Stacks.Thickenings.SquareZeroExtension (𝟙 (firstOrderThickeningScheme T Y f)) where
  A := secondOrderThickeningSheaf T Y f
  π := ⟨secondOrderThickeningProj T Y f⟩
  locallySurjective_π :=
    CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ _
      (fun _ x => ⟨secondOrderExtMk (sqZeroExtFst x) (sqZeroExtSnd x) 0 0, rfl⟩)
  inclusion := ⟨{ base := 𝟙 _, c := secondOrderThickeningProj T Y f }⟩
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := ⟨{ base := 𝟙 _, c := secondOrderThickeningQ₀₁ T Y f }⟩
  over_base := by
    apply SheafedSpace.forgetToPresheafedSpace.map_injective
    refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
    ext W x
    exact sqZeroExt_ext rfl rfl
  I := secondOrderKerSheaf T Y f
  quasicoherent := secondOrderKerSheaf_isQuasicoherent T Y f
  ι := secondOrderThickeningInr T Y f
  naturality _ _ :=
    secondOrderExt_ext (map_zero _).symm (map_zero _).symm rfl rfl
  mem_kernel _ _ := sqZeroExt_ext rfl rfl
  exact_kernel W a ha := by
    refine ⟨secondOrderKerMk (secondOrderExtRight a) (secondOrderExtTop a), ?_, ?_⟩
    · exact secondOrderExt_ext (congrArg sqZeroExtFst ha).symm
        (congrArg sqZeroExtSnd ha).symm rfl rfl
    · intro y hy
      exact secondOrderKer_ext (congrArg secondOrderExtRight hy)
        (congrArg secondOrderExtTop hy)
  smul_lift W a x := secondOrderThickeningInr_smul T Y f W a x
  square_zero W _ _ :=
    secondOrderExt_mul_eq_zero_of_fst_left (firstOrderThickeningOpen T Y f W) rfl rfl rfl rfl

/-! ### The scheme `T''` -/

/-- A realization of the square-zero extension as a first-order thickening of schemes over `T'`;
it exists because `K` is quasi-coherent. -/
public abbrev secondOrderThickeningRealization :
    Stacks.Thickenings.Realization (secondOrderThickeningExtension T Y f) :=
  (Stacks.Thickenings.squareZeroExtension_realization
    (secondOrderThickeningExtension T Y f)).some

/-- The topological space of `T` carrying the sheaf of rings `𝒪_{T''}`. -/
public abbrev secondOrderThickeningSheafedSpace : SheafedSpace CommRingCat.{u} :=
  Stacks.Thickenings.thickenedSpace (firstOrderThickeningScheme T Y f)
    (secondOrderThickeningExtension T Y f).A

/-- The space of `T` carrying `𝒪_{T''}`, as a locally ringed space: its stalks are local rings
because the realization of the extension is a scheme on an isomorphic sheafed space. -/
public abbrev secondOrderThickeningLocallyRingedSpace : LocallyRingedSpace.{u} where
  toSheafedSpace := secondOrderThickeningSheafedSpace T Y f
  isLocalRing x := by
    let e := (secondOrderThickeningRealization T Y f).sheafedIso
    have : IsIso e.inv.hom := SheafedSpace.forgetToPresheafedSpace.map_isIso e.inv
    have := PresheafedSpace.stalkMap.isIso e.inv.hom x
    exact (asIso (e.inv.hom.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

/-- The realization of the extension is isomorphic, as a locally ringed space, to the space of
`T` carrying `𝒪_{T''}`. -/
public abbrev secondOrderThickeningIso :
    (secondOrderThickeningRealization T Y f).ambient.toLocallyRingedSpace ≅
      secondOrderThickeningLocallyRingedSpace T Y f :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (secondOrderThickeningRealization T Y f).sheafedIso

/-- **The second-order universal thickening `T''` as a scheme.**  The topological space of `T`
equipped with the structure sheaf
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`; it is a scheme because it is isomorphic,
as a locally ringed space, to the realization of the square-zero extension of `𝒪_{T'}` by
`K`. -/
@[stacks 07J3 "the second-order thickening T'' as a scheme"]
public def secondOrderThickeningScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (secondOrderThickeningLocallyRingedSpace T Y f) (by
    intro x
    obtain ⟨R, g, hg, y, hy⟩ :=
      Scheme.exists_Spec_apply_eq ((secondOrderThickeningIso T Y f).inv.base x)
    refine ⟨R, g.toLRSHom ≫ (secondOrderThickeningIso T Y f).hom, ⟨y, ?_⟩, ?_⟩
    · change (secondOrderThickeningIso T Y f).hom.base (g.base y) = x
      rw [hy]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => q.base) (secondOrderThickeningIso T Y f).inv_hom_id) x
    · exact LocallyRingedSpace.IsOpenImmersion.comp g.toLRSHom
        (secondOrderThickeningIso T Y f).hom)

/-- **`T''` has the same underlying space as `T`, hence the same opens.**  The identity function,
recorded so that an open of `T''` can be read as an open of `T` without transport. -/
public abbrev secondOrderThickeningOpen
    (W : (Opens ↑(secondOrderThickeningScheme T Y f))ᵒᵖ) : (Opens ↑T.scheme)ᵒᵖ := W

/-- **An open of `T` read as an open of `T''`**, the two schemes having the same underlying
space.  The identity function. -/
public abbrev secondOrderThickeningOpen' (W : Opens ↑T.scheme) :
    Opens ↑(secondOrderThickeningScheme T Y f) := W

/-- The sections of the structure sheaf of `T''` over an open are the sections of
`𝒪_{T''}`. -/
public theorem secondOrderThickeningScheme_obj
    (W : (Opens ↑(secondOrderThickeningScheme T Y f))ᵒᵖ) :
    (secondOrderThickeningScheme T Y f).presheaf.obj W =
      (secondOrderThickeningPresheaf T Y f).obj (secondOrderThickeningOpen T Y f W) := rfl

/-! ### The morphisms of schemes -/

/-- **The immersion `j : T' ⟶ T''`**, whose map on sections is the projection
`𝒪_{T''} ⟶ 𝒪_{T'}`. -/
@[stacks 07J3 "the immersion T' ⟶ T'' of schemes"]
public def secondOrderThickeningι :
    firstOrderThickeningScheme T Y f ⟶ secondOrderThickeningScheme T Y f :=
  ⟨LocallyRingedSpace.homMk (secondOrderThickeningExtension T Y f).inclusion (by
    have he : ((secondOrderThickeningRealization T Y f).immersion.toLRSHom ≫
          (secondOrderThickeningIso T Y f).hom).toShHom =
        (secondOrderThickeningExtension T Y f).inclusion :=
      (secondOrderThickeningRealization T Y f).inclusion_eq
    rw [← he]
    intro x
    exact ((secondOrderThickeningRealization T Y f).immersion.toLRSHom ≫
      (secondOrderThickeningIso T Y f).hom).prop x)⟩

/-- **The immersion `T ⟶ T''`**: the immersion `T ⟶ T'` followed by `T' ⟶ T''`.  Its map on
sections is `Crystalline.secondOrderThickeningFstProj`, the projection `𝒪_{T''} ⟶ 𝒪_T`. -/
@[stacks 07J3 "the immersion T ⟶ T'' of schemes"]
public def secondOrderThickeningιT : T.scheme ⟶ secondOrderThickeningScheme T Y f :=
  firstOrderThickeningι T Y f ≫ secondOrderThickeningι T Y f

/-- A map of sheaves of rings `𝒪_{T'} ⟶ 𝒪_{T''}`, read as a morphism of sheafed spaces
`T'' ⟶ T'`; the two spaces are equal, so only the map of sheaves carries information. -/
public def secondOrderThickeningRawHom
    (g : firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f) :
    secondOrderThickeningSheafedSpace T Y f ⟶
      (firstOrderThickeningScheme T Y f).toSheafedSpace :=
  ⟨{ base := 𝟙 _, c := g }⟩

/-- **A map of sheaves of rings `𝒪_{T'} ⟶ 𝒪_{T''}` whose composite with the projection
`𝒪_{T''} ⟶ 𝒪_{T'}` is the map on sections of a morphism of schemes `T' ⟶ T'` induces a local
homomorphism on every stalk.**  Composing with the immersion `T' ⟶ T''` recovers that morphism,
so the induced stalk map has a retraction through a local homomorphism, and a ring map whose
composite with another is local is itself local. -/
public theorem secondOrderThickeningRawHom_isLocalHom
    (g : firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f)
    (ψ : (firstOrderThickeningScheme T Y f).toLocallyRingedSpace ⟶
      (firstOrderThickeningScheme T Y f).toLocallyRingedSpace)
    (hg : (secondOrderThickeningExtension T Y f).inclusion ≫
      secondOrderThickeningRawHom T Y f g = ψ.toShHom)
    (x : ↑(firstOrderThickeningScheme T Y f)) :
    IsLocalHom (((secondOrderThickeningRawHom T Y f g).hom.stalkMap x).hom) := by
  have hlocal : IsLocalHom ((((secondOrderThickeningExtension T Y f).inclusion.hom ≫
      (secondOrderThickeningRawHom T Y f g).hom).stalkMap x).hom) :=
    LocallyRingedSpace.isLocalHom_stalkMap_congr _ _ hg.symm x
      (LocallyRingedSpace.isLocalHomStalkMap ψ x)
  have hstalk : ((((secondOrderThickeningExtension T Y f).inclusion.hom ≫
        (secondOrderThickeningRawHom T Y f g).hom).stalkMap x).hom) =
      (((secondOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom).comp
        (((secondOrderThickeningRawHom T Y f g).hom.stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.comp (secondOrderThickeningExtension T Y f).inclusion.hom
      (secondOrderThickeningRawHom T Y f g).hom x]
    rfl
  have hcomp : IsLocalHom
      ((((secondOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom).comp
        (((secondOrderThickeningRawHom T Y f g).hom.stalkMap x).hom)) := by
    rw [← hstalk]
    exact hlocal
  exact isLocalHom_of_comp (((secondOrderThickeningRawHom T Y f g).hom.stalkMap x).hom)
    (((secondOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom)

/-- **`q₀₂` splits the projection onto `𝒪_{T'}`**, as `q₀₁` does. -/
public theorem secondOrderThickeningQ₀₂_comp_proj :
    secondOrderThickeningQ₀₂ T Y f ≫ secondOrderThickeningProj T Y f = 𝟙 _ :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ =>
    sqZeroExt_ext rfl rfl))

/-- **The composite of `q₁₂` with the projection onto `𝒪_{T'}` is `p₁` after the projection
`𝒪_{T'} ⟶ 𝒪_T`**: `(g, ω) ↦ (g, d g)`.  Unlike `q₀₁` and `q₀₂`, the map `q₁₂` does not split
the projection. -/
public theorem secondOrderThickeningQ₁₂_comp_proj :
    secondOrderThickeningQ₁₂ T Y f ≫ secondOrderThickeningProj T Y f =
      firstOrderThickeningProj T Y f ≫ firstOrderThickeningP₁ T Y f :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ =>
    sqZeroExt_ext rfl rfl))

/-- **The morphism `q₀₁ : T'' ⟶ T'`**, induced by the map `(g, ω) ↦ (g, ω, 0, 0)` of structure
sheaves. -/
@[stacks 07J3 "the morphism q₀₁ : T'' ⟶ T' of schemes"]
public def secondOrderThickeningQ₀₁Hom :
    secondOrderThickeningScheme T Y f ⟶ firstOrderThickeningScheme T Y f :=
  ⟨LocallyRingedSpace.homMk
    (secondOrderThickeningRawHom T Y f (secondOrderThickeningQ₀₁ T Y f))
    (secondOrderThickeningRawHom_isLocalHom T Y f (secondOrderThickeningQ₀₁ T Y f)
      (Scheme.Hom.toLRSHom (𝟙 (firstOrderThickeningScheme T Y f))) (by
        apply SheafedSpace.forgetToPresheafedSpace.map_injective
        refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
        ext W x
        exact sqZeroExt_ext rfl rfl))⟩

/-- **The morphism `q₀₂ : T'' ⟶ T'`**, induced by the map `(g, ω) ↦ (g, ω, ω, 0)` of structure
sheaves. -/
@[stacks 07J3 "the morphism q₀₂ : T'' ⟶ T' of schemes"]
public def secondOrderThickeningQ₀₂Hom :
    secondOrderThickeningScheme T Y f ⟶ firstOrderThickeningScheme T Y f :=
  ⟨LocallyRingedSpace.homMk
    (secondOrderThickeningRawHom T Y f (secondOrderThickeningQ₀₂ T Y f))
    (secondOrderThickeningRawHom_isLocalHom T Y f (secondOrderThickeningQ₀₂ T Y f)
      (Scheme.Hom.toLRSHom (𝟙 (firstOrderThickeningScheme T Y f))) (by
        apply SheafedSpace.forgetToPresheafedSpace.map_injective
        refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
        ext W x
        exact sqZeroExt_ext rfl rfl))⟩

/-- **The morphism `q₁₂ : T'' ⟶ T'`**, induced by the map
`(g, ω) ↦ (g, d g, ω, d ω)` of structure sheaves. -/
@[stacks 07J3 "the morphism q₁₂ : T'' ⟶ T' of schemes"]
public def secondOrderThickeningQ₁₂Hom :
    secondOrderThickeningScheme T Y f ⟶ firstOrderThickeningScheme T Y f :=
  ⟨LocallyRingedSpace.homMk
    (secondOrderThickeningRawHom T Y f (secondOrderThickeningQ₁₂ T Y f))
    (secondOrderThickeningRawHom_isLocalHom T Y f (secondOrderThickeningQ₁₂ T Y f)
      (Scheme.Hom.toLRSHom
        (firstOrderThickeningP₁Hom T Y f ≫ firstOrderThickeningι T Y f)) (by
        apply SheafedSpace.forgetToPresheafedSpace.map_injective
        refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
        ext W x
        exact sqZeroExt_ext rfl rfl))⟩

/-- **The morphism `q₀ : T'' ⟶ T`**, the composite of `q₀₁` with `p₀`; on sections this is the
relation `q₀ = q₀₁ ∘ p₀` of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the morphism q₀ : T'' ⟶ T of schemes"]
public def secondOrderThickeningQ₀Hom : secondOrderThickeningScheme T Y f ⟶ T.scheme :=
  secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningProjHom T Y f

/-- **The morphism `q₁ : T'' ⟶ T`**, the composite of `q₀₁` with `p₁`; on sections this is the
relation `q₁ = q₀₁ ∘ p₁`. -/
@[stacks 07J3 "the morphism q₁ : T'' ⟶ T of schemes"]
public def secondOrderThickeningQ₁Hom : secondOrderThickeningScheme T Y f ⟶ T.scheme :=
  secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f

/-- **The morphism `q₂ : T'' ⟶ T`**, the composite of `q₁₂` with `p₁`; on sections this is the
relation `q₂ = q₁₂ ∘ p₁`. -/
@[stacks 07J3 "the morphism q₂ : T'' ⟶ T of schemes"]
public def secondOrderThickeningQ₂Hom : secondOrderThickeningScheme T Y f ⟶ T.scheme :=
  secondOrderThickeningQ₁₂Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f

/-! ### The composition relations for schemes -/

/-- **`q₀` acts on sections by the map `q₀ : 𝒪_T ⟶ 𝒪_{T''}`** of the sheaf-level
construction. -/
@[simp]
public theorem secondOrderThickeningQ₀Hom_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (secondOrderThickeningQ₀Hom T Y f).c.app W = (secondOrderThickeningQ₀ T Y f).app W := rfl

/-- **`q₁` acts on sections by the map `q₁ : 𝒪_T ⟶ 𝒪_{T''}`.** -/
@[simp]
public theorem secondOrderThickeningQ₁Hom_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (secondOrderThickeningQ₁Hom T Y f).c.app W = (secondOrderThickeningQ₁ T Y f).app W := rfl

/-- **`q₂` acts on sections by the map `q₂ : 𝒪_T ⟶ 𝒪_{T''}`.** -/
@[simp]
public theorem secondOrderThickeningQ₂Hom_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (secondOrderThickeningQ₂Hom T Y f).c.app W = (secondOrderThickeningQ₂ T Y f).app W :=
  congrArg (fun φ : T.scheme.sheaf.obj ⟶ secondOrderThickeningPresheaf T Y f => φ.app W)
    (secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁ T Y f)

/-- **`q₀₁` acts on sections by the map `q₀₁ : 𝒪_{T'} ⟶ 𝒪_{T''}`.** -/
@[simp]
public theorem secondOrderThickeningQ₀₁Hom_c_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (secondOrderThickeningQ₀₁Hom T Y f).c.app W =
      (secondOrderThickeningQ₀₁ T Y f).app (firstOrderThickeningOpen T Y f W) := rfl

/-- **`q₀₂` acts on sections by the map `q₀₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`.** -/
@[simp]
public theorem secondOrderThickeningQ₀₂Hom_c_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (secondOrderThickeningQ₀₂Hom T Y f).c.app W =
      (secondOrderThickeningQ₀₂ T Y f).app (firstOrderThickeningOpen T Y f W) := rfl

/-- **`q₁₂` acts on sections by the map `q₁₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`.** -/
@[simp]
public theorem secondOrderThickeningQ₁₂Hom_c_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (secondOrderThickeningQ₁₂Hom T Y f).c.app W =
      (secondOrderThickeningQ₁₂ T Y f).app (firstOrderThickeningOpen T Y f W) := rfl

/-- **The immersion `T' ⟶ T''` acts on sections by the projection `𝒪_{T''} ⟶ 𝒪_{T'}`.** -/
@[simp]
public theorem secondOrderThickeningι_c_app
    (W : (Opens ↑(secondOrderThickeningScheme T Y f))ᵒᵖ) :
    (secondOrderThickeningι T Y f).c.app W =
      (secondOrderThickeningProj T Y f).app (secondOrderThickeningOpen T Y f W) := rfl

/-- **Two morphisms of schemes `T'' ⟶ T` built from maps of structure sheaves are equal as soon
as those maps are.**  Both are presented as a map `𝒪_{T'} ⟶ 𝒪_{T''}` followed by a map
`𝒪_T ⟶ 𝒪_{T'}`, and the hypothesis is the equality of the two composites; the underlying maps of
spaces are identities on both sides.  The three composition relations of [Stacks, Tag 07J3] that
are not definitional all reduce to this. -/
public theorem secondOrderThickeningHomT_ext
    {a b : secondOrderThickeningScheme T Y f ⟶ T.scheme}
    (g h : firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f)
    (u v : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f)
    (ha : a.toLRSHom.toHom =
      (secondOrderThickeningRawHom T Y f g ≫ firstOrderThickeningRawHom T Y f u).hom)
    (hb : b.toLRSHom.toHom =
      (secondOrderThickeningRawHom T Y f h ≫ firstOrderThickeningRawHom T Y f v).hom)
    (huv : u ≫ g = v ≫ h) : a = b := by
  refine congrArg Scheme.Hom.mk (LocallyRingedSpace.Hom.ext' (ha.trans (Eq.trans ?_ hb.symm)))
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  ext W z
  exact congrArg (fun φ : T.scheme.sheaf.obj ⟶ secondOrderThickeningPresheaf T Y f =>
    (φ.app (op W)).hom z) huv

/-- **`q₀ = q₀₁ ∘ p₀` for schemes**, the first relation of [Stacks, Tag 07J3]; it holds by the
definition of `q₀`. -/
@[stacks 07J3 "the relation q₀ = q₀₁ ∘ p₀, for schemes"]
public theorem secondOrderThickeningQ₀Hom_eq_Q₀₁_comp_P₀ :
    secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningProjHom T Y f =
      secondOrderThickeningQ₀Hom T Y f := rfl

/-- **`q₁ = q₀₁ ∘ p₁` for schemes**; it holds by the definition of `q₁`. -/
@[stacks 07J3 "the relation q₁ = q₀₁ ∘ p₁, for schemes"]
public theorem secondOrderThickeningQ₁Hom_eq_Q₀₁_comp_P₁ :
    secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f =
      secondOrderThickeningQ₁Hom T Y f := rfl

/-- **`q₂ = q₁₂ ∘ p₁` for schemes**; it holds by the definition of `q₂`. -/
@[stacks 07J3 "the relation q₂ = q₁₂ ∘ p₁, for schemes"]
public theorem secondOrderThickeningQ₂Hom_eq_Q₁₂_comp_P₁ :
    secondOrderThickeningQ₁₂Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f =
      secondOrderThickeningQ₂Hom T Y f := rfl

/-- **`q₁ = q₁₂ ∘ p₀` for schemes**, which on sections is
`Crystalline.secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀`. -/
@[stacks 07J3 "the relation q₁ = q₁₂ ∘ p₀, for schemes"]
public theorem secondOrderThickeningQ₁Hom_eq_Q₁₂_comp_P₀ :
    secondOrderThickeningQ₁₂Hom T Y f ≫ firstOrderThickeningProjHom T Y f =
      secondOrderThickeningQ₁Hom T Y f :=
  secondOrderThickeningHomT_ext T Y f (secondOrderThickeningQ₁₂ T Y f)
    (secondOrderThickeningQ₀₁ T Y f) (firstOrderThickeningP₀ T Y f)
    (firstOrderThickeningP₁ T Y f) rfl rfl
    ((secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀ T Y f).trans
      (secondOrderThickeningQ₁_eq_Q₀₁_comp_P₁ T Y f).symm)

/-- **`q₀ = q₀₂ ∘ p₀` for schemes**, which on sections is
`Crystalline.secondOrderThickeningQ₀_eq_Q₀₂_comp_P₀`. -/
@[stacks 07J3 "the relation q₀ = q₀₂ ∘ p₀, for schemes"]
public theorem secondOrderThickeningQ₀Hom_eq_Q₀₂_comp_P₀ :
    secondOrderThickeningQ₀₂Hom T Y f ≫ firstOrderThickeningProjHom T Y f =
      secondOrderThickeningQ₀Hom T Y f :=
  secondOrderThickeningHomT_ext T Y f (secondOrderThickeningQ₀₂ T Y f)
    (secondOrderThickeningQ₀₁ T Y f) (firstOrderThickeningP₀ T Y f)
    (firstOrderThickeningP₀ T Y f) rfl rfl
    ((secondOrderThickeningQ₀_eq_Q₀₂_comp_P₀ T Y f).trans
      (secondOrderThickeningQ₀_eq_Q₀₁_comp_P₀ T Y f).symm)

/-- **`q₂ = q₀₂ ∘ p₁` for schemes**, which on sections is
`Crystalline.secondOrderThickeningQ₂_eq_Q₀₂_comp_P₁`. -/
@[stacks 07J3 "the relation q₂ = q₀₂ ∘ p₁, for schemes"]
public theorem secondOrderThickeningQ₂Hom_eq_Q₀₂_comp_P₁ :
    secondOrderThickeningQ₀₂Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f =
      secondOrderThickeningQ₂Hom T Y f :=
  secondOrderThickeningHomT_ext T Y f (secondOrderThickeningQ₀₂ T Y f)
    (secondOrderThickeningQ₁₂ T Y f) (firstOrderThickeningP₁ T Y f)
    (firstOrderThickeningP₁ T Y f) rfl rfl
    ((secondOrderThickeningQ₂_eq_Q₀₂_comp_P₁ T Y f).trans
      (secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁ T Y f).symm)

/-! ### The order of the thickening -/

/-- The immersion `T' ⟶ T''` is a closed immersion: its map on sections is the projection
`𝒪_{T''} ⟶ 𝒪_{T'}`, which is surjective on every open and hence on every stalk, and it is a
closed embedding, being the identity on the underlying space. -/
public instance secondOrderThickeningι_isClosedImmersion :
    IsClosedImmersion (secondOrderThickeningι T Y f) := by
  have hsurj : SurjectiveOnStalks (secondOrderThickeningι T Y f) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨W, hxW, s, rfl⟩ :=
      (firstOrderThickeningScheme T Y f).presheaf.exists_germ_eq y
    refine ⟨(secondOrderThickeningScheme T Y f).presheaf.germ
      (secondOrderThickeningOpen' T Y f W) x hxW
      (secondOrderExtMk (q := dpWedge T Y f) (sqZeroExtFst s) (sqZeroExtSnd s) 0 0), ?_⟩
    exact (Scheme.Hom.germ_stalkMap_apply (secondOrderThickeningι T Y f)
      (secondOrderThickeningOpen' T Y f W) x hxW _).trans rfl
  exact ⟨(Homeomorph.refl _).isClosedEmbedding⟩

/-- **`T' ⟶ T''` is a first-order thickening of schemes**: its ideal sheaf has square zero,
because the kernel of `𝒪_{T''} ⟶ 𝒪_{T'}` over every open is the square-zero ideal
`K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`. -/
@[stacks 07J3 "T' ⟶ T'' is a first-order thickening of schemes"]
public theorem secondOrderThickeningι_isFirstOrderThickening :
    Stacks.Thickenings.IsFirstOrderThickening (secondOrderThickeningι T Y f) := by
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  rw [show ((secondOrderThickeningι T Y f).ker ^ 2).ideal V =
      ((secondOrderThickeningι T Y f).ker.ideal V) ^ 2 from rfl, Scheme.Hom.ker_apply]
  exact secondOrderThickening_ker_proj_sq T Y f (firstOrderThickeningOpen T Y f (op V.1))

/-- The immersion `T ⟶ T''` is a closed immersion, being the composite of the closed immersions
`T ⟶ T'` and `T' ⟶ T''`. -/
public instance secondOrderThickeningιT_isClosedImmersion :
    IsClosedImmersion (secondOrderThickeningιT T Y f) :=
  inferInstanceAs (IsClosedImmersion
    (firstOrderThickeningι T Y f ≫ secondOrderThickeningι T Y f))

/-- **`T → T''` is a second-order thickening of schemes**, which is the description of `T''` in
[Stacks, Tag 07J3].  The ideal sheaf of `T ⟶ T''` is the kernel of `𝒪_{T''} ⟶ 𝒪_T`, whose cube
vanishes on every open by `Crystalline.secondOrderThickening_ker_cube`.

The order is *not* obtained by composing the two first-order thickenings `T ⟶ T'` and
`T' ⟶ T''`: a composite of two first-order thickenings is in general only of order three — for
`Z = Spec k[x]/(x⁴)`, the closed subschemes cut out by `(x²)` and by `(x)` give first-order
thickenings whose composite has `(x)³ ≠ 0` — and what makes the order here two is the explicit
vanishing of the cube in the sheaf-level computation. -/
@[stacks 07J3 "T → T'' is a second-order thickening of schemes"]
public theorem secondOrderThickeningιT_isNthOrderThickening :
    Stacks.Thickenings.IsNthOrderThickening 2 (secondOrderThickeningιT T Y f) := by
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  rw [show ((secondOrderThickeningιT T Y f).ker ^ 3).ideal V =
      ((secondOrderThickeningιT T Y f).ker.ideal V) ^ 3 from rfl, Scheme.Hom.ker_apply]
  exact secondOrderThickening_ker_cube T Y f (secondOrderThickeningOpen T Y f (op V.1))

/-- `T ⟶ T''` is a thickening of schemes. -/
public theorem secondOrderThickeningιT_isThickening :
    Stacks.Thickenings.IsThickening (secondOrderThickeningιT T Y f) :=
  (secondOrderThickeningιT_isNthOrderThickening T Y f).isThickening

/-! ### Retracting the immersion `T ⟶ T''` -/

/-- A map of sheaves of rings `𝒪_{T'} ⟶ 𝒪_T`, read as a morphism of sheafed spaces `T ⟶ T'`;
the two spaces are equal, so only the map of sheaves carries information. -/
public def firstOrderThickeningRawHomFromT
    (c : firstOrderThickeningPresheaf T Y f ⟶ T.scheme.sheaf.obj) :
    T.scheme.toSheafedSpace ⟶ (firstOrderThickeningScheme T Y f).toSheafedSpace :=
  ⟨{ base := 𝟙 _, c := c }⟩

/-- **Two morphisms of schemes `T ⟶ T'` presented by maps of structure sheaves are equal as soon
as those maps are.**  Stated so that each of the two presentations is compared with a *small*
term, which is what keeps the comparison tractable. -/
public theorem firstOrderThickeningHomFromT_ext
    {a b : T.scheme ⟶ firstOrderThickeningScheme T Y f}
    (c d : firstOrderThickeningPresheaf T Y f ⟶ T.scheme.sheaf.obj)
    (ha : a.toLRSHom.toHom = (firstOrderThickeningRawHomFromT T Y f c).hom)
    (hb : b.toLRSHom.toHom = (firstOrderThickeningRawHomFromT T Y f d).hom)
    (hcd : c = d) : a = b :=
  congrArg Scheme.Hom.mk (LocallyRingedSpace.Hom.ext'
    (ha.trans ((congrArg (fun φ => (firstOrderThickeningRawHomFromT T Y f φ).hom) hcd).trans
      hb.symm)))

/-- The map on sections of the immersion `T ⟶ T''` is the projection `𝒪_{T''} ⟶ 𝒪_T`. -/
public theorem secondOrderThickeningιT_toHom :
    (secondOrderThickeningιT T Y f).toLRSHom.toHom =
      (⟨{ base := 𝟙 _, c := secondOrderThickeningFstProj T Y f }⟩ :
        T.scheme.toSheafedSpace ⟶ secondOrderThickeningSheafedSpace T Y f).hom := by
  refine PresheafedSpace.hext _ _ rfl ?_
  apply heq_of_eq
  ext W x
  rfl

/-- A morphism `T'' ⟶ T'` given by a map of sheaves `g` whose composite with the projection
`𝒪_{T''} ⟶ 𝒪_T` is the projection `𝒪_{T'} ⟶ 𝒪_T` retracts the immersion `T ⟶ T''`. -/
private theorem secondOrderThickeningιT_comp_eq_ι
    {a : secondOrderThickeningScheme T Y f ⟶ firstOrderThickeningScheme T Y f}
    (g : firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f)
    (ha : a.toLRSHom.toHom = (secondOrderThickeningRawHom T Y f g).hom)
    (hg : g ≫ secondOrderThickeningFstProj T Y f = firstOrderThickeningProj T Y f) :
    secondOrderThickeningιT T Y f ≫ a = firstOrderThickeningι T Y f :=
  firstOrderThickeningHomFromT_ext T Y f (g ≫ secondOrderThickeningFstProj T Y f)
    (firstOrderThickeningProj T Y f)
    (by
      rw [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toHom, ha]
      refine PresheafedSpace.hext _ _ rfl ?_
      apply heq_of_eq
      ext W x
      rfl)
    (by
      refine PresheafedSpace.hext _ _ rfl ?_
      apply heq_of_eq
      ext W x
      rfl)
    hg

/-- **`q₀₁` retracts the immersion `T ⟶ T''` onto the immersion `T ⟶ T'`.** -/
public theorem secondOrderThickeningιT_comp_Q₀₁Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₀₁Hom T Y f =
      firstOrderThickeningι T Y f :=
  secondOrderThickeningιT_comp_eq_ι T Y f (secondOrderThickeningQ₀₁ T Y f) rfl
    (NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))

/-- **`q₀₂` retracts the immersion `T ⟶ T''` onto the immersion `T ⟶ T'`.** -/
public theorem secondOrderThickeningιT_comp_Q₀₂Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₀₂Hom T Y f =
      firstOrderThickeningι T Y f :=
  secondOrderThickeningιT_comp_eq_ι T Y f (secondOrderThickeningQ₀₂ T Y f) rfl
    (NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))

/-- **`q₁₂` retracts the immersion `T ⟶ T''` onto the immersion `T ⟶ T'`.** -/
public theorem secondOrderThickeningιT_comp_Q₁₂Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₁₂Hom T Y f =
      firstOrderThickeningι T Y f :=
  secondOrderThickeningιT_comp_eq_ι T Y f (secondOrderThickeningQ₁₂ T Y f) rfl
    (NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))

/-- **`q₀` retracts the immersion `T ⟶ T''`.** -/
@[stacks 07J3 "the relation q₀ ∘ (T ⟶ T'') = id"]
public theorem secondOrderThickeningιT_comp_Q₀Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₀Hom T Y f = 𝟙 T.scheme := by
  rw [show secondOrderThickeningQ₀Hom T Y f =
    secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningProjHom T Y f from rfl,
    ← Category.assoc, secondOrderThickeningιT_comp_Q₀₁Hom,
    firstOrderThickeningι_comp_projHom]

/-- **`q₁` retracts the immersion `T ⟶ T''`.** -/
@[stacks 07J3 "the relation q₁ ∘ (T ⟶ T'') = id"]
public theorem secondOrderThickeningιT_comp_Q₁Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₁Hom T Y f = 𝟙 T.scheme := by
  rw [show secondOrderThickeningQ₁Hom T Y f =
    secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f from rfl,
    ← Category.assoc, secondOrderThickeningιT_comp_Q₀₁Hom,
    firstOrderThickeningι_comp_P₁Hom]

/-- **`q₂` retracts the immersion `T ⟶ T''`.** -/
@[stacks 07J3 "the relation q₂ ∘ (T ⟶ T'') = id"]
public theorem secondOrderThickeningιT_comp_Q₂Hom :
    secondOrderThickeningιT T Y f ≫ secondOrderThickeningQ₂Hom T Y f = 𝟙 T.scheme := by
  rw [show secondOrderThickeningQ₂Hom T Y f =
    secondOrderThickeningQ₁₂Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f from rfl,
    ← Category.assoc, secondOrderThickeningιT_comp_Q₁₂Hom,
    firstOrderThickeningι_comp_P₁Hom]

/-- **`q₁` and `q₀` agree over the base `Y`**, because `p₁` and `p₀` do. -/
public theorem secondOrderThickeningQ₁Hom_comp_base :
    secondOrderThickeningQ₁Hom T Y f ≫ f = secondOrderThickeningQ₀Hom T Y f ≫ f := by
  rw [show secondOrderThickeningQ₁Hom T Y f =
      secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f from rfl,
    show secondOrderThickeningQ₀Hom T Y f =
      secondOrderThickeningQ₀₁Hom T Y f ≫ firstOrderThickeningProjHom T Y f from rfl,
    Category.assoc, Category.assoc, firstOrderThickeningP₁Hom_comp_base]

/-- **`q₂` and `q₀` agree over the base `Y`.** -/
public theorem secondOrderThickeningQ₂Hom_comp_base :
    secondOrderThickeningQ₂Hom T Y f ≫ f = secondOrderThickeningQ₀Hom T Y f ≫ f := by
  rw [show secondOrderThickeningQ₂Hom T Y f =
      secondOrderThickeningQ₁₂Hom T Y f ≫ firstOrderThickeningP₁Hom T Y f from rfl,
    Category.assoc, firstOrderThickeningP₁Hom_comp_base, ← Category.assoc,
    secondOrderThickeningQ₁Hom_eq_Q₁₂_comp_P₀, secondOrderThickeningQ₁Hom_comp_base]

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S)

/-! ### The divided power scheme `T''` -/

/-- **The extended ideal `J''` as a sheaf of ideals on `T''`**: the sections of `𝒪_{T''}` whose
component in `𝒪_T` lies in the divided power ideal `J` of `T`. -/
@[stacks 07J3 "the ideal J'' as a sheaf of ideals on T''"]
public def secondOrderThickeningIdealSheaf :
    (SheafOfModules.unit (secondOrderThickeningScheme A.thickening.target S.S.scheme
      A.toBase.hom).ringCatSheaf).Submodule where
  obj W := secondOrderThickeningIdeal A.thickening.target S.S.scheme A.toBase.hom
    (secondOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
  map {_ _} i := fun _ hx => A.thickening.target.ideal.map i hx
  isSheaf {_} x hx := A.thickening.target.ideal.isSheaf (secondOrderExtFst x) hx

/-- The immersion `U ⟶ T''`: the immersion `U ⟶ T` followed by `T ⟶ T''`. -/
public def secondOrderThickeningSourceι :
    A.thickening.source ⟶
      secondOrderThickeningScheme A.thickening.target S.S.scheme A.toBase.hom :=
  A.thickening.immersion ≫
    secondOrderThickeningιT A.thickening.target S.S.scheme A.toBase.hom

/-- The immersion `U ⟶ T''` is a closed immersion, as a composite of two closed immersions. -/
public instance secondOrderThickeningSourceι_isClosedImmersion :
    IsClosedImmersion (secondOrderThickeningSourceι S A) :=
  inferInstanceAs (IsClosedImmersion (A.thickening.immersion ≫
    secondOrderThickeningιT A.thickening.target S.S.scheme A.toBase.hom))

/-- The immersion `U ⟶ T''` is surjective, `U ⟶ T` and `T ⟶ T''` both being so. -/
public theorem secondOrderThickeningSourceι_surjective :
    Function.Surjective (secondOrderThickeningSourceι S A) := by
  intro z
  obtain ⟨y, hy⟩ := (secondOrderThickeningιT_isThickening A.thickening.target S.S.scheme
    A.toBase.hom).2 z
  obtain ⟨x, hx⟩ := A.thickening.isThickening.2 y
  refine ⟨x, ?_⟩
  rw [show (secondOrderThickeningSourceι S A) x =
    (secondOrderThickeningιT A.thickening.target S.S.scheme A.toBase.hom)
      (A.thickening.immersion x) from rfl, hx, hy]

/-- **The extended ideal `J''` is the ideal sheaf of the immersion `U ⟶ T''`**: a section
`(g, ω₁, ω₂, η)` of `𝒪_{T''}` dies on `U` exactly when `g` does, because the immersion `U ⟶ T''`
acts on sections through the projection `𝒪_{T''} ⟶ 𝒪_T`. -/
public theorem secondOrderThickeningIdealSheaf_eq_moduleKernel :
    secondOrderThickeningIdealSheaf S A =
      moduleKernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit
          (secondOrderThickeningSourceι S A).toRingCatSheafHom) := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro W
  apply Submodule.ext
  intro x
  show secondOrderExtFst x ∈ A.thickening.target.ideal.obj
      (secondOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W) ↔
    A.thickening.immersion.c.app
      (secondOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
      (secondOrderExtFst x) = 0
  exact Iff.of_eq (congrArg
    (fun I : (SheafOfModules.unit A.thickening.target.scheme.ringCatSheaf).Submodule =>
      secondOrderExtFst x ∈ I.obj
        (secondOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W))
    (thickening_ideal_eq_moduleKernel S A))

/-- **The extended ideal `J''` is quasi-coherent**, being the ideal sheaf of the closed immersion
`U ⟶ T''`. -/
@[stacks 07J3 "the ideal J'' is quasi-coherent"]
public theorem secondOrderThickeningIdealSheaf_isQuasicoherent :
    (secondOrderThickeningIdealSheaf S A).toSheafOfModules.IsQuasicoherent := by
  rw [secondOrderThickeningIdealSheaf_eq_moduleKernel]
  exact (SheafOfModules.isQuasicoherent (secondOrderThickeningScheme A.thickening.target
    S.S.scheme A.toBase.hom).ringCatSheaf).prop_of_iso
      (moduleKernelSubmoduleIso _).symm inferInstance

/-- **The divided power scheme `(T'', J'', δ'')`.**  The scheme `T''`, the quasi-coherent ideal
`J''` and the divided power structure `δ''` of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "T'' with the ideal J'' and the divided powers δ'' is a divided power scheme"]
public abbrev secondOrderThickeningDPScheme : DividedPowerScheme.{u} where
  scheme := secondOrderThickeningScheme A.thickening.target S.S.scheme A.toBase.hom
  ideal := secondOrderThickeningIdealSheaf S A
  isQuasicoherent := secondOrderThickeningIdealSheaf_isQuasicoherent S A
  dividedPowers :=
    { dividedPowers W :=
        secondOrderThickeningDividedPowers A.thickening.target S.S.scheme A.toBase.hom
          (secondOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
      naturality i :=
        secondOrderThickening_restriction_isDPMorphism A.thickening.target S.S.scheme
          A.toBase.hom i }

/-! ### The six morphisms of divided power schemes -/

/-- **`q₀ : T'' ⟶ T` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₀ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₀DP :
    secondOrderThickeningDPScheme S A ⟶ A.thickening.target where
  hom := secondOrderThickeningQ₀Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := secondOrderThickeningQ₀_isDPMorphism
    A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`q₁ : T'' ⟶ T` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₁ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₁DP :
    secondOrderThickeningDPScheme S A ⟶ A.thickening.target where
  hom := secondOrderThickeningQ₁Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := secondOrderThickeningQ₁_isDPMorphism
    A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`q₂ : T'' ⟶ T` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₂ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₂DP :
    secondOrderThickeningDPScheme S A ⟶ A.thickening.target where
  hom := secondOrderThickeningQ₂Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := by
    have h := secondOrderThickeningQ₂_isDPMorphism
      A.thickening.target S.S.scheme A.toBase.hom (op W)
    rwa [← secondOrderThickeningQ₂Hom_c_app] at h

/-- **`q₀₁ : T'' ⟶ T'` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₀₁ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₀₁DP :
    secondOrderThickeningDPScheme S A ⟶ firstOrderThickeningDPScheme S A where
  hom := secondOrderThickeningQ₀₁Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := secondOrderThickeningQ₀₁_isDPMorphism
    A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`q₀₂ : T'' ⟶ T'` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₀₂ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₀₂DP :
    secondOrderThickeningDPScheme S A ⟶ firstOrderThickeningDPScheme S A where
  hom := secondOrderThickeningQ₀₂Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := secondOrderThickeningQ₀₂_isDPMorphism
    A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`q₁₂ : T'' ⟶ T'` is a morphism of divided power schemes.** -/
@[stacks 07J3 "q₁₂ is a morphism of divided power schemes"]
public def secondOrderThickeningQ₁₂DP :
    secondOrderThickeningDPScheme S A ⟶ firstOrderThickeningDPScheme S A where
  hom := secondOrderThickeningQ₁₂Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W := secondOrderThickeningQ₁₂_isDPMorphism
    A.thickening.target S.S.scheme A.toBase.hom (op W)

/-! ### The object `(U, T'', δ'')` of `CRIS(X/S)` -/

/-- **The divided power thickening `U ⟶ T''`**: a thickening of schemes whose defining ideal is
the divided power ideal `J''`. -/
@[stacks 07J3 "U ⟶ T'' is a divided power thickening"]
public abbrev secondOrderThickeningSchemeThickening : SchemeThickening.{u} where
  source := A.thickening.source
  target := secondOrderThickeningDPScheme S A
  immersion := secondOrderThickeningSourceι S A
  isThickening := ⟨secondOrderThickeningSourceι_isClosedImmersion S A,
    secondOrderThickeningSourceι_surjective S A⟩
  ideal_eq_ker V := by
    rw [Scheme.Hom.ker_apply]
    exact congrArg (fun I : (SheafOfModules.unit (secondOrderThickeningScheme
      A.thickening.target S.S.scheme A.toBase.hom).ringCatSheaf).Submodule =>
        I.obj (op V.1)) (secondOrderThickeningIdealSheaf_eq_moduleKernel S A)

/-- **`(U, T'', δ'')` is an object of `CRIS(X/S)`.**  This is the final assertion of
[Stacks, Tag 07J3]: the second-order universal thickening of an object of the crystalline
category is again an object of it.  `T''` with the ideal
`J'' = J ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` and the divided powers `δ''` of the remark is a
divided power scheme, `U ⟶ T''` is a divided power thickening, and `T'' ⟶ S` is `q₀` followed by
the structure morphism of `T`. -/
@[stacks 07J3 "(U, T'', δ'') is an object of CRIS(X/S)"]
public abbrev secondOrderThickeningObject : Thickening S where
  thickening := secondOrderThickeningSchemeThickening S A
  toBase := secondOrderThickeningQ₀DP S A ≫ A.toBase
  toX := A.toX
  over_base := by
    rw [DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningSchemeThickening S A).immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, ← Category.assoc (secondOrderThickeningιT
      A.thickening.target S.S.scheme A.toBase.hom),
      secondOrderThickeningιT_comp_Q₀Hom, Category.id_comp]
    exact A.over_base

/-! ### The six morphisms of `CRIS(X/S)` -/

/-- **The morphism `q₀ : (U, T'', δ'') ⟶ (U, T, δ)` of `CRIS(X/S)`.** -/
@[stacks 07J3 "the morphism q₀ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₀ : secondOrderThickeningObject S A ⟶ A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₀DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₀Hom, Category.comp_id]
  base_naturality := rfl
  toX_naturality := Category.id_comp _

/-- **The morphism `q₁ : (U, T'', δ'') ⟶ (U, T, δ)` of `CRIS(X/S)`.**  It is a morphism over the
divided power base because `q₁` and `q₀` agree after composing with the structure morphism of
`T`. -/
@[stacks 07J3 "the morphism q₁ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₁ : secondOrderThickeningObject S A ⟶ A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₁DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₁DP S A).hom = secondOrderThickeningQ₁Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₁Hom, Category.comp_id]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningQ₁DP S A).hom = secondOrderThickeningQ₁Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl]
    exact secondOrderThickeningQ₁Hom_comp_base A.thickening.target S.S.scheme A.toBase.hom
  toX_naturality := Category.id_comp _

/-- **The morphism `q₂ : (U, T'', δ'') ⟶ (U, T, δ)` of `CRIS(X/S)`.** -/
@[stacks 07J3 "the morphism q₂ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₂ : secondOrderThickeningObject S A ⟶ A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₂DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₂DP S A).hom = secondOrderThickeningQ₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₂Hom, Category.comp_id]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningQ₂DP S A).hom = secondOrderThickeningQ₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl]
    exact secondOrderThickeningQ₂Hom_comp_base A.thickening.target S.S.scheme A.toBase.hom
  toX_naturality := Category.id_comp _

/-- **The morphism `q₀₁ : (U, T'', δ'') ⟶ (U, T', δ')` of `CRIS(X/S)`.** -/
@[stacks 07J3 "the morphism q₀₁ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₀₁ :
    secondOrderThickeningObject S A ⟶ firstOrderThickeningObject S A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₀₁DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ firstOrderThickeningι
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀₁DP S A).hom = secondOrderThickeningQ₀₁Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₀₁Hom]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningQ₀₁DP S A).hom = secondOrderThickeningQ₀₁Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom = firstOrderThickeningProjHom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      ← Category.assoc, secondOrderThickeningQ₀Hom_eq_Q₀₁_comp_P₀]
  toX_naturality := Category.id_comp _

/-- **The morphism `q₀₂ : (U, T'', δ'') ⟶ (U, T', δ')` of `CRIS(X/S)`.** -/
@[stacks 07J3 "the morphism q₀₂ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₀₂ :
    secondOrderThickeningObject S A ⟶ firstOrderThickeningObject S A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₀₂DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ firstOrderThickeningι
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀₂DP S A).hom = secondOrderThickeningQ₀₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₀₂Hom]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningQ₀₂DP S A).hom = secondOrderThickeningQ₀₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom = firstOrderThickeningProjHom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      ← Category.assoc, secondOrderThickeningQ₀Hom_eq_Q₀₂_comp_P₀]
  toX_naturality := Category.id_comp _

/-- **The morphism `q₁₂ : (U, T'', δ'') ⟶ (U, T', δ')` of `CRIS(X/S)`.** -/
@[stacks 07J3 "the morphism q₁₂ of CRIS(X/S)"]
public def secondOrderThickeningSiteQ₁₂ :
    secondOrderThickeningObject S A ⟶ firstOrderThickeningObject S A where
  sourceHom := 𝟙 _
  targetHom := secondOrderThickeningQ₁₂DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (secondOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ secondOrderThickeningιT
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningObject S A).thickening.immersion =
      A.thickening.immersion ≫ firstOrderThickeningι
        A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₁₂DP S A).hom = secondOrderThickeningQ₁₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, secondOrderThickeningιT_comp_Q₁₂Hom]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      DividedPowerScheme.Hom.comp_hom,
      show (secondOrderThickeningQ₁₂DP S A).hom = secondOrderThickeningQ₁₂Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom = firstOrderThickeningProjHom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (secondOrderThickeningQ₀DP S A).hom = secondOrderThickeningQ₀Hom
      A.thickening.target S.S.scheme A.toBase.hom from rfl,
      ← Category.assoc, secondOrderThickeningQ₁Hom_eq_Q₁₂_comp_P₀,
      secondOrderThickeningQ₁Hom_comp_base]
  toX_naturality := Category.id_comp _

/-! ### The composition relations in `CRIS(X/S)` -/
/-- **`q₀ = q₀₁ ∘ p₀` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₀ = q₀₁ ∘ p₀ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₀₁_comp_P₀ :
    secondOrderThickeningSiteQ₀₁ S A ≫ firstOrderThickeningSiteP₀ S A =
      secondOrderThickeningSiteQ₀ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₀Hom_eq_Q₀₁_comp_P₀ A.thickening.target S.S.scheme A.toBase.hom))

/-- **`q₁ = q₀₁ ∘ p₁` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₁ = q₀₁ ∘ p₁ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₀₁_comp_P₁ :
    secondOrderThickeningSiteQ₀₁ S A ≫ firstOrderThickeningSiteP₁ S A =
      secondOrderThickeningSiteQ₁ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₁Hom_eq_Q₀₁_comp_P₁ A.thickening.target S.S.scheme A.toBase.hom))

/-- **`q₁ = q₁₂ ∘ p₀` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₁ = q₁₂ ∘ p₀ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₁₂_comp_P₀ :
    secondOrderThickeningSiteQ₁₂ S A ≫ firstOrderThickeningSiteP₀ S A =
      secondOrderThickeningSiteQ₁ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₁Hom_eq_Q₁₂_comp_P₀ A.thickening.target S.S.scheme A.toBase.hom))

/-- **`q₂ = q₁₂ ∘ p₁` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₂ = q₁₂ ∘ p₁ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₁₂_comp_P₁ :
    secondOrderThickeningSiteQ₁₂ S A ≫ firstOrderThickeningSiteP₁ S A =
      secondOrderThickeningSiteQ₂ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₂Hom_eq_Q₁₂_comp_P₁ A.thickening.target S.S.scheme A.toBase.hom))

/-- **`q₀ = q₀₂ ∘ p₀` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₀ = q₀₂ ∘ p₀ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₀₂_comp_P₀ :
    secondOrderThickeningSiteQ₀₂ S A ≫ firstOrderThickeningSiteP₀ S A =
      secondOrderThickeningSiteQ₀ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₀Hom_eq_Q₀₂_comp_P₀ A.thickening.target S.S.scheme A.toBase.hom))

/-- **`q₂ = q₀₂ ∘ p₁` in `CRIS(X/S)`**, one of the six relations of [Stacks, Tag 07J3]. -/
@[stacks 07J3 "the relation q₂ = q₀₂ ∘ p₁ in CRIS(X/S)"]
public theorem secondOrderThickeningSiteQ₀₂_comp_P₁ :
    secondOrderThickeningSiteQ₀₂ S A ≫ firstOrderThickeningSiteP₁ S A =
      secondOrderThickeningSiteQ₂ S A :=
  Thickening.Hom.ext (Category.id_comp _) (DividedPowerScheme.Hom.ext
    (secondOrderThickeningQ₂Hom_eq_Q₀₂_comp_P₁ A.thickening.target S.S.scheme A.toBase.hom))

/-! ### The object and the diagram in the small crystalline site -/

variable (B : CrystallineThickening S)

/-- **`(U, T'', δ'')` is an object of the small crystalline category `Cris(X/S)`** whenever
`(U, T, δ)` is.  The construction leaves the map `U ⟶ X` untouched, so it is still an open
immersion; this is the assertion of [Stacks, Tag 07J3] in the category in which the remark states
it. -/
@[stacks 07J3 "(U, T'', δ'') is an object of Cris(X/S)"]
public def secondOrderThickeningCrysObject : CrystallineThickening S :=
  ⟨secondOrderThickeningObject S B.obj, B.property⟩

/-- **The morphism `q₀ : (U, T'', δ'') ⟶ (U, T, δ)` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₀ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₀ : secondOrderThickeningCrysObject S B ⟶ B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₀ S B.obj)

/-- **The morphism `q₁ : (U, T'', δ'') ⟶ (U, T, δ)` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₁ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₁ : secondOrderThickeningCrysObject S B ⟶ B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₁ S B.obj)

/-- **The morphism `q₂ : (U, T'', δ'') ⟶ (U, T, δ)` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₂ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₂ : secondOrderThickeningCrysObject S B ⟶ B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₂ S B.obj)

/-- **The morphism `q₀₁ : (U, T'', δ'') ⟶ (U, T', δ')` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₀₁ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₀₁ :
    secondOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₀₁ S B.obj)

/-- **The morphism `q₀₂ : (U, T'', δ'') ⟶ (U, T', δ')` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₀₂ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₀₂ :
    secondOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₀₂ S B.obj)

/-- **The morphism `q₁₂ : (U, T'', δ'') ⟶ (U, T', δ')` of `Cris(X/S)`.** -/
@[stacks 07J3 "the morphism q₁₂ of the diagram in Cris(X/S)"]
public def secondOrderThickeningCrysQ₁₂ :
    secondOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S B :=
  ObjectProperty.homMk (secondOrderThickeningSiteQ₁₂ S B.obj)

/-- **`q₀ = q₀₁ ∘ p₀` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₀ = q₀₁ ∘ p₀ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₀₁_comp_P₀ :
    secondOrderThickeningCrysQ₀₁ S B ≫ firstOrderThickeningCrysP₀ S B =
      secondOrderThickeningCrysQ₀ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₀₁_comp_P₀ S B.obj

/-- **`q₁ = q₀₁ ∘ p₁` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₁ = q₀₁ ∘ p₁ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₀₁_comp_P₁ :
    secondOrderThickeningCrysQ₀₁ S B ≫ firstOrderThickeningCrysP₁ S B =
      secondOrderThickeningCrysQ₁ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₀₁_comp_P₁ S B.obj

/-- **`q₁ = q₁₂ ∘ p₀` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₁ = q₁₂ ∘ p₀ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₁₂_comp_P₀ :
    secondOrderThickeningCrysQ₁₂ S B ≫ firstOrderThickeningCrysP₀ S B =
      secondOrderThickeningCrysQ₁ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₁₂_comp_P₀ S B.obj

/-- **`q₂ = q₁₂ ∘ p₁` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₂ = q₁₂ ∘ p₁ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₁₂_comp_P₁ :
    secondOrderThickeningCrysQ₁₂ S B ≫ firstOrderThickeningCrysP₁ S B =
      secondOrderThickeningCrysQ₂ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₁₂_comp_P₁ S B.obj

/-- **`q₀ = q₀₂ ∘ p₀` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₀ = q₀₂ ∘ p₀ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₀₂_comp_P₀ :
    secondOrderThickeningCrysQ₀₂ S B ≫ firstOrderThickeningCrysP₀ S B =
      secondOrderThickeningCrysQ₀ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₀₂_comp_P₀ S B.obj

/-- **`q₂ = q₀₂ ∘ p₁` in `Cris(X/S)`.** -/
@[stacks 07J3 "the relation q₂ = q₀₂ ∘ p₁ in Cris(X/S)"]
public theorem secondOrderThickeningCrysQ₀₂_comp_P₁ :
    secondOrderThickeningCrysQ₀₂ S B ≫ firstOrderThickeningCrysP₁ S B =
      secondOrderThickeningCrysQ₂ S B :=
  ObjectProperty.hom_ext _ <|secondOrderThickeningSiteQ₀₂_comp_P₁ S B.obj

end GlobalCrystallineSituation

end Crystalline

end
