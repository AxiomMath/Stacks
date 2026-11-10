module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# The first-order universal thickening as an object of the crystalline site

Let `(U, T, δ)` be an object of the big crystalline category `CRIS(X/S)` of a global crystalline
situation.  `StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickenings.lean` builds the
structure sheaf `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}` of the first-order universal thickening of `T`, the
ideal `J' = J ⊕ Ω_{T/S,δ}`, its divided power structure `δ'`, and the two maps `p₀`, `p₁`
together with the projection.  All of that is a construction with *sheaves* of rings.  This
module turns it into geometry: `Ω_{T/S,δ}` is a quasi-coherent `𝒪_T`-module, so the square-zero
extension `𝒪_{T'}` of `𝒪_T` is the structure sheaf of a scheme `T'` on the topological space of
`T`, and `(U, T', δ')` is an object of `CRIS(X/S)` sitting in the diagram

```
         T
      /  |  \
    id   i   id
    /    |    \
   T  ←  T'  →  T
      p₀    p₁
```

of the site, in which `i` is a first-order thickening whose ideal sheaf is `Ω_{T/S,δ}`.

## Main definitions

* `Crystalline.firstOrderThickeningExtension` — the square-zero extension of `𝒪_T` by
  `Ω_{T/Y,δ}`, in the sense of `Stacks.Thickenings.SquareZeroExtension`.
* `Crystalline.firstOrderThickeningScheme` — the scheme `T'`, with structure sheaf `𝒪_{T'}` on
  the topological space of `T`.
* `Crystalline.firstOrderThickeningι`, `Crystalline.firstOrderThickeningProjHom` and
  `Crystalline.firstOrderThickeningP₁Hom` — the morphisms of schemes `i : T ⟶ T'` and
  `p₀, p₁ : T' ⟶ T`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningDPScheme` — the divided power
  scheme `(T', J', δ')`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningObject` — the object
  `(U, T', δ')` of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteι`,
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteP₀` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteP₁` — the three morphisms of
  `CRIS(X/S)` in the diagram.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysObject` — the same object in
  the small crystalline category `Cris(X/S)`, with
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysι`,
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysP₀` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysP₁` its three morphisms.

## Main results

* `Crystalline.firstOrderThickeningScheme_obj` — the sections of the structure sheaf of `T'` are
  the sections of `𝒪_{T'}`.
* `Crystalline.firstOrderThickeningι_isFirstOrderThickening` — `i : T ⟶ T'` is a first-order
  thickening of schemes.
* `Crystalline.firstOrderThickeningι_comp_projHom` and
  `Crystalline.firstOrderThickeningι_comp_P₁Hom` — both `p₀` and `p₁` retract `i`.
* `Crystalline.firstOrderThickeningP₁Hom_comp_base` — `p₀` and `p₁` agree over the base `Y`,
  because the universal divided power derivation kills every section pulled back from `Y`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteι_comp_P₀` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteι_comp_P₁` — the relations of
  the diagram of [Stacks, Tag 07J2], in `CRIS(X/S)`, and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysι_comp_P₀` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysι_comp_P₁` the same in
  `Cris(X/S)`.
* `Crystalline.firstOrderThickeningιKernelEquiv` — the ideal sheaf of `i` is `Ω_{T/Y,δ}`, and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteKernelEquiv` — for an object of
  the site, that it is the restriction `(Ω_{X/S})_T` of the crystalline differentials.

## Implementation notes

The realization of a square-zero extension of the structure sheaf as a scheme is
`Stacks.Thickenings.squareZeroExtension_realization` [Stacks, Tag 05YV], whose hypothesis is that
the kernel of the extension is a quasi-coherent module; here the kernel is `Ω_{T/Y,δ}`, which is
quasi-coherent by `Crystalline.dpDifferentialsSheaf_isQuasicoherent` [Stacks, Tag 07IY].  That
theorem only asserts a realization to exist, and the realization it produces has a structure
sheaf merely *isomorphic* to `𝒪_{T'}`.  `Crystalline.firstOrderThickeningScheme` is therefore
built on the locally ringed space whose structure sheaf *is* `𝒪_{T'}`; the realization is used
only to transport the two properties of that space which are not immediate, namely that its
stalks are local rings and that it is locally an affine scheme.  Consequently every statement
about sections of `𝒪_{T'}` below is a statement about the sheaf of the previous module, holding
with no transport, and the opens of `T'` are the opens of `T` — an identification recorded by
`Crystalline.firstOrderThickeningOpen`, which is the identity function.

The structure morphism used in forming the square-zero extension is `𝟙 T.scheme`.  This is not a
restriction: `Stacks.Thickenings.SquareZeroExtension f` uses `f` only to record that the
extension lies over the base, and taking the base to be `T` itself turns that record into the
statement that `p₀` retracts `i`, which is one of the relations of the diagram.  The morphism
`T' ⟶ S` of the site is then `p₀` followed by the structure morphism of `T`, and `p₁` is a
morphism over `S` as well because `p₁` and `p₀` agree on sections pulled back from the base.

Quasi-coherence of `J'` is proved, as in the source, by identifying `J'` with the ideal sheaf of
the closed immersion `U ⟶ T'`.  This is why the divided power scheme `T'` is constructed for an
object of the site rather than for a bare divided power scheme `T`, whose divided power ideal
need not be the ideal of any thickening.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
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

/-! ### The square-zero extension datum -/

/-- The inclusion of `Ω_{T/Y,δ}` into the sections of `𝒪_{T'}` as the square-zero summand. -/
public def firstOrderThickeningInr (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpDifferentialsModules T Y f).obj W) →+
      ↑((firstOrderThickeningPresheaf T Y f).obj W) where
  toFun ω := sqZeroExtMk 0 ω
  map_zero' := rfl
  map_add' _ _ := sqZeroExt_ext (add_zero (0 : ↑(T.scheme.sheaf.obj.obj W))).symm rfl

/-- Multiplying a square-zero section of `𝒪_{T'}` by an arbitrary one scales the differential by
the first coordinate: `a * (0, ω) = (0, a₀ · ω)`. -/
public theorem mul_firstOrderThickeningInr (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑((firstOrderThickeningPresheaf T Y f).obj W))
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    a * firstOrderThickeningInr T Y f W ω =
      firstOrderThickeningInr T Y f W (sqZeroExtFst a • ω) :=
  sqZeroExt_ext (mul_zero (sqZeroExtFst a))
    (by
      change sqZeroExtFst a • ω + (0 : ↑(T.scheme.sheaf.obj.obj W)) • sqZeroExtSnd a =
        sqZeroExtFst a • ω
      rw [zero_smul, add_zero])

/-- **The square-zero extension of `𝒪_T` by `Ω_{T/Y,δ}`.**  The structure sheaf `𝒪_{T'}` of the
first-order universal thickening, its projection onto `𝒪_T`, and the quasi-coherent kernel
`Ω_{T/Y,δ}` of that projection, packaged as the input of the realization theorem
[Stacks, Tag 05YV].  The base is taken to be `T` itself, with `p₀` as the structure map. -/
public def firstOrderThickeningExtension :
    Stacks.Thickenings.SquareZeroExtension (𝟙 T.scheme) where
  A := firstOrderThickeningSheaf T Y f
  π := ⟨firstOrderThickeningProj T Y f⟩
  locallySurjective_π :=
    CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ _
      (fun _ x => ⟨sqZeroExtMk x 0, rfl⟩)
  inclusion := ⟨{ base := 𝟙 _, c := firstOrderThickeningProj T Y f }⟩
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := ⟨{ base := 𝟙 _, c := firstOrderThickeningP₀ T Y f }⟩
  over_base := by
    apply SheafedSpace.forgetToPresheafedSpace.map_injective
    refine PresheafedSpace.hext _ _ ?_ ?_
    · rfl
    · apply heq_of_eq
      ext W x
      rfl
  I := dpDifferentialsSheaf T Y f
  quasicoherent := dpDifferentialsSheaf_isQuasicoherent T Y f
  ι := firstOrderThickeningInr T Y f
  naturality _ _ := sqZeroExt_ext (map_zero _).symm rfl
  mem_kernel _ _ := rfl
  exact_kernel _ a ha :=
    ⟨sqZeroExtSnd a, sqZeroExt_ext ha.symm rfl, fun _ hy => congrArg sqZeroExtSnd hy⟩
  smul_lift W a x := (mul_firstOrderThickeningInr T Y f W a x).symm
  square_zero W _ _ := firstOrderThickening_mul_eq_zero T Y f W rfl rfl

/-! ### The scheme `T'` -/

/-- A realization of the square-zero extension as a first-order thickening of schemes; it exists
because `Ω_{T/Y,δ}` is quasi-coherent. -/
public abbrev firstOrderThickeningRealization :
    Stacks.Thickenings.Realization (firstOrderThickeningExtension T Y f) :=
  (Stacks.Thickenings.squareZeroExtension_realization
    (firstOrderThickeningExtension T Y f)).some

/-- The topological space of `T` carrying the sheaf of rings `𝒪_{T'}`. -/
public abbrev firstOrderThickeningSheafedSpace : SheafedSpace CommRingCat.{u} :=
  Stacks.Thickenings.thickenedSpace T.scheme (firstOrderThickeningExtension T Y f).A

/-- The space of `T` carrying `𝒪_{T'}`, as a locally ringed space: its stalks are local rings
because the realization of the extension is a scheme on an isomorphic sheafed space. -/
public abbrev firstOrderThickeningLocallyRingedSpace : LocallyRingedSpace.{u} where
  toSheafedSpace := firstOrderThickeningSheafedSpace T Y f
  isLocalRing x := by
    let e := (firstOrderThickeningRealization T Y f).sheafedIso
    have : IsIso e.inv.hom := SheafedSpace.forgetToPresheafedSpace.map_isIso e.inv
    have := PresheafedSpace.stalkMap.isIso e.inv.hom x
    exact (asIso (e.inv.hom.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

/-- The realization of the extension is isomorphic, as a locally ringed space, to the space of
`T` carrying `𝒪_{T'}`. -/
public abbrev firstOrderThickeningIso :
    (firstOrderThickeningRealization T Y f).ambient.toLocallyRingedSpace ≅
      firstOrderThickeningLocallyRingedSpace T Y f :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (firstOrderThickeningRealization T Y f).sheafedIso

/-- **The first-order universal thickening `T'` as a scheme.**  The topological space of `T`
equipped with the structure sheaf `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}`; it is a scheme because it is
isomorphic, as a locally ringed space, to the realization of the square-zero extension. -/
@[stacks 07J2 "the first-order thickening T' as a scheme"]
public def firstOrderThickeningScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (firstOrderThickeningLocallyRingedSpace T Y f) (by
    intro x
    obtain ⟨R, g, hg, y, hy⟩ :=
      Scheme.exists_Spec_apply_eq ((firstOrderThickeningIso T Y f).inv.base x)
    refine ⟨R, g.toLRSHom ≫ (firstOrderThickeningIso T Y f).hom, ⟨y, ?_⟩, ?_⟩
    · change (firstOrderThickeningIso T Y f).hom.base (g.base y) = x
      rw [hy]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => q.base) (firstOrderThickeningIso T Y f).inv_hom_id) x
    · exact LocallyRingedSpace.IsOpenImmersion.comp g.toLRSHom
        (firstOrderThickeningIso T Y f).hom)

/-- **`T'` has the same underlying space as `T`, hence the same opens.**  The identity function,
recorded so that an open of `T'` can be read as an open of `T` without transport. -/
public abbrev firstOrderThickeningOpen
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) : (Opens ↑T.scheme)ᵒᵖ := W

/-- **An open of `T` read as an open of `T'`**, the two schemes having the same underlying
space.  The identity function. -/
public abbrev firstOrderThickeningOpen' (W : Opens ↑T.scheme) :
    Opens ↑(firstOrderThickeningScheme T Y f) := W

/-- The sections of the structure sheaf of `T'` over an open are the sections of `𝒪_{T'}`. -/
public theorem firstOrderThickeningScheme_obj
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (firstOrderThickeningScheme T Y f).presheaf.obj W =
      (firstOrderThickeningPresheaf T Y f).obj (firstOrderThickeningOpen T Y f W) := rfl

/-! ### The morphisms of schemes `i`, `p₀` and `p₁` -/

/-- **The immersion `i : T ⟶ T'`**, whose map on sections is the projection
`𝒪_{T'} ⟶ 𝒪_T`. -/
@[stacks 07J2 "the immersion i : T ⟶ T' of schemes"]
public def firstOrderThickeningι : T.scheme ⟶ firstOrderThickeningScheme T Y f :=
  ⟨LocallyRingedSpace.homMk (firstOrderThickeningExtension T Y f).inclusion (by
    have he : ((firstOrderThickeningRealization T Y f).immersion.toLRSHom ≫
          (firstOrderThickeningIso T Y f).hom).toShHom =
        (firstOrderThickeningExtension T Y f).inclusion :=
      (firstOrderThickeningRealization T Y f).inclusion_eq
    rw [← he]
    intro x
    exact ((firstOrderThickeningRealization T Y f).immersion.toLRSHom ≫
      (firstOrderThickeningIso T Y f).hom).prop x)⟩

/-- A map of sheaves of rings `𝒪_T ⟶ 𝒪_{T'}`, read as a morphism of sheafed spaces `T' ⟶ T`;
the two spaces are equal, so only the map of sheaves carries information. -/
public def firstOrderThickeningRawHom
    (g : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f) :
    firstOrderThickeningSheafedSpace T Y f ⟶ T.scheme.toSheafedSpace :=
  ⟨{ base := 𝟙 _, c := g }⟩

/-- Following the inclusion of the square-zero extension by a section `g` of the projection
gives the identity. -/
private theorem inclusion_comp_rawHom
    (g : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f)
    (hg : g ≫ firstOrderThickeningProj T Y f = 𝟙 T.scheme.sheaf.obj) :
    (firstOrderThickeningExtension T Y f).inclusion ≫ firstOrderThickeningRawHom T Y f g =
      (Scheme.Hom.toLRSHom (𝟙 T.scheme : T.scheme ⟶ T.scheme)).toShHom := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  refine PresheafedSpace.hext _ _ ?_ ?_
  · rfl
  · apply heq_of_eq
    ext W a
    exact congrArg
      (fun φ : T.scheme.sheaf.obj ⟶ T.scheme.sheaf.obj => (φ.app (op W)).hom a) hg

/-- A section of the projection `𝒪_{T'} ⟶ 𝒪_T` induces a local homomorphism on every stalk:
composing it with the immersion recovers the identity, so the induced stalk map has a retraction,
and a ring map with a retraction reflects units. -/
public theorem firstOrderThickeningRawHom_isLocalHom
    (g : T.scheme.sheaf.obj ⟶ firstOrderThickeningPresheaf T Y f)
    (hg : g ≫ firstOrderThickeningProj T Y f = 𝟙 T.scheme.sheaf.obj) (x : ↑T.scheme) :
    IsLocalHom (((firstOrderThickeningRawHom T Y f g).hom.stalkMap x).hom) := by
  have hsh := inclusion_comp_rawHom T Y f g hg
  have hlocal : IsLocalHom ((((firstOrderThickeningExtension T Y f).inclusion.hom ≫
      (firstOrderThickeningRawHom T Y f g).hom).stalkMap x).hom) :=
    LocallyRingedSpace.isLocalHom_stalkMap_congr _ _ hsh.symm x
      (LocallyRingedSpace.isLocalHomStalkMap
        (Scheme.Hom.toLRSHom (𝟙 T.scheme : T.scheme ⟶ T.scheme)) x)
  have hstalk : ((((firstOrderThickeningExtension T Y f).inclusion.hom ≫
        (firstOrderThickeningRawHom T Y f g).hom).stalkMap x).hom) =
      (((firstOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningRawHom T Y f g).hom.stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.comp]
    rfl
  have hcomp : IsLocalHom
      ((((firstOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningRawHom T Y f g).hom.stalkMap x).hom)) := by
    rw [← hstalk]
    exact hlocal
  exact isLocalHom_of_comp (((firstOrderThickeningRawHom T Y f g).hom.stalkMap x).hom)
    (((firstOrderThickeningExtension T Y f).inclusion.hom.stalkMap x).hom)

/-- **The morphism `p₀ : T' ⟶ T`**, induced by the inclusion `g ↦ (g, 0)` of structure
sheaves. -/
@[stacks 07J2 "the morphism p₀ : T' ⟶ T of schemes"]
public def firstOrderThickeningProjHom : firstOrderThickeningScheme T Y f ⟶ T.scheme :=
  ⟨LocallyRingedSpace.homMk (firstOrderThickeningRawHom T Y f (firstOrderThickeningP₀ T Y f))
    (firstOrderThickeningRawHom_isLocalHom T Y f (firstOrderThickeningP₀ T Y f)
      (firstOrderThickeningP₀_comp_proj T Y f))⟩

/-- **The morphism `p₁ : T' ⟶ T`**, induced by the derivation-shifted inclusion
`g ↦ (g, d_{T/Y,δ} g)` of structure sheaves. -/
@[stacks 07J2 "the morphism p₁ : T' ⟶ T of schemes"]
public def firstOrderThickeningP₁Hom : firstOrderThickeningScheme T Y f ⟶ T.scheme :=
  ⟨LocallyRingedSpace.homMk (firstOrderThickeningRawHom T Y f (firstOrderThickeningP₁ T Y f))
    (firstOrderThickeningRawHom_isLocalHom T Y f (firstOrderThickeningP₁ T Y f)
      (firstOrderThickeningP₁_comp_proj T Y f))⟩

/-- **The morphism `p₀` of schemes acts on sections by the map `p₀ : 𝒪_T ⟶ 𝒪_{T'}`** of the
previous module, so every statement there about `p₀` is a statement about this morphism. -/
@[simp]
public theorem firstOrderThickeningProjHom_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (firstOrderThickeningProjHom T Y f).c.app W = (firstOrderThickeningP₀ T Y f).app W := rfl

/-- **The morphism `p₁` of schemes acts on sections by the map `p₁ : 𝒪_T ⟶ 𝒪_{T'}`** of the
previous module.  In particular `Crystalline.firstOrderThickeningP₁_sub_P₀`, that `p₁ - p₀` is
the universal divided power derivation followed by the inclusion of `Ω_{T/Y,δ}`, is a statement
about these two morphisms of schemes. -/
@[simp]
public theorem firstOrderThickeningP₁Hom_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (firstOrderThickeningP₁Hom T Y f).c.app W = (firstOrderThickeningP₁ T Y f).app W := rfl

/-- **The immersion `i` acts on sections by the projection `𝒪_{T'} ⟶ 𝒪_T`** of the previous
module, so every statement there about the projection is a statement about `i`. -/
@[simp]
public theorem firstOrderThickeningι_c_app
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    (firstOrderThickeningι T Y f).c.app W =
      (firstOrderThickeningProj T Y f).app (firstOrderThickeningOpen T Y f W) := rfl

/-- **`p₀` retracts the immersion `i`.** -/
@[stacks 07J2 "the diagram relation p₀ ∘ i = id, for schemes"]
public theorem firstOrderThickeningι_comp_projHom :
    firstOrderThickeningι T Y f ≫ firstOrderThickeningProjHom T Y f = 𝟙 T.scheme := by
  exact congrArg Scheme.Hom.mk (LocallyRingedSpace.Hom.ext' (congrArg (·.hom)
    (inclusion_comp_rawHom T Y f _ (firstOrderThickeningP₀_comp_proj T Y f))))

/-- **`p₁` retracts the immersion `i`.** -/
@[stacks 07J2 "the diagram relation p₁ ∘ i = id, for schemes"]
public theorem firstOrderThickeningι_comp_P₁Hom :
    firstOrderThickeningι T Y f ≫ firstOrderThickeningP₁Hom T Y f = 𝟙 T.scheme := by
  exact congrArg Scheme.Hom.mk (LocallyRingedSpace.Hom.ext' (congrArg (·.hom)
    (inclusion_comp_rawHom T Y f _ (firstOrderThickeningP₁_comp_proj T Y f))))

/-- The immersion `T ⟶ T'` is a closed immersion: its map on sections is the projection
`𝒪_{T'} ⟶ 𝒪_T`, which is surjective on every open and hence on every stalk, and it is a closed
embedding, being the identity on the underlying space. -/
public instance firstOrderThickeningι_isClosedImmersion :
    IsClosedImmersion (firstOrderThickeningι T Y f) := by
  have hsurj : SurjectiveOnStalks (firstOrderThickeningι T Y f) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨W, hxW, s, rfl⟩ := T.scheme.presheaf.exists_germ_eq y
    exact ⟨(firstOrderThickeningScheme T Y f).presheaf.germ
      (firstOrderThickeningOpen' T Y f W) x hxW (sqZeroExtMk s 0),
      Scheme.Hom.germ_stalkMap_apply (firstOrderThickeningι T Y f)
        (firstOrderThickeningOpen' T Y f W) x hxW (sqZeroExtMk s 0)⟩
  exact ⟨(Homeomorph.refl _).isClosedEmbedding⟩

/-- **The immersion `T ⟶ T'` is a first-order thickening of schemes**: its ideal sheaf has
square zero, because the kernel of `𝒪_{T'} ⟶ 𝒪_T` over every open is the square-zero summand
`Ω_{T/Y,δ}`. -/
@[stacks 07J2 "i : T ⟶ T' is a first-order thickening of schemes"]
public theorem firstOrderThickeningι_isFirstOrderThickening :
    Stacks.Thickenings.IsFirstOrderThickening (firstOrderThickeningι T Y f) := by
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  rw [show ((firstOrderThickeningι T Y f).ker ^ 2).ideal V =
      ((firstOrderThickeningι T Y f).ker.ideal V) ^ 2 from rfl, Scheme.Hom.ker_apply]
  exact firstOrderThickening_ker_sq T Y f (firstOrderThickeningOpen T Y f (op V.1))

/-- `T ⟶ T'` is a thickening of schemes. -/
public theorem firstOrderThickeningι_isThickening :
    Stacks.Thickenings.IsThickening (firstOrderThickeningι T Y f) :=
  (firstOrderThickeningι_isFirstOrderThickening T Y f).isThickening

/-- **The ideal sheaf of `i : T ⟶ T'` is `Ω_{T/Y,δ}`**: over every open, the kernel of the map
on sections of `i` is canonically the module of divided power differentials. -/
@[stacks 07J2 "the ideal sheaf of i is the sheaf of divided power differentials"]
public def firstOrderThickeningιKernelEquiv
    (W : (Opens ↑(firstOrderThickeningScheme T Y f))ᵒᵖ) :
    ↑((dpDifferentialsModules T Y f).obj (firstOrderThickeningOpen T Y f W)) ≃+
      RingHom.ker (((firstOrderThickeningι T Y f).c.app W).hom) :=
  firstOrderThickeningKernelEquiv T Y f (firstOrderThickeningOpen T Y f W)

/-! ### Agreement of `p₀` and `p₁` over the base -/

/-- **The universal divided power derivation kills every section pulled back from the base.**
This is the defining property of the divided power differentials *relative* to `Y`. -/
public theorem sheafApp_eq_zero_of_mem_baseSections (W : T.scheme.Opens)
    {b : Γ(T.scheme, W)} (hb : b ∈ baseSections T Y f W) : sheafApp T Y f W b = 0 := by
  have hd : (presheafD T Y f W).d b = 0 :=
    dpConstD_base (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W)) hb
  change (dpDifferentialsToSheaf T Y f).app (op W) ((presheafD T Y f W).d b) = 0
  rw [hd]
  exact map_zero _

/-- The universal divided power derivation kills the image of a section of `𝒪_Y`. -/
public theorem sheafApp_app (V : Y.Opens) (a : Γ(Y, V)) :
    sheafApp T Y f (f ⁻¹ᵁ V) (f.app V a) = 0 := by
  refine sheafApp_eq_zero_of_mem_baseSections T Y f (f ⁻¹ᵁ V) ?_
  rw [← Scheme.Hom.appLE_eq_app (f := f) (U := V)]
  exact appLE_mem_baseSections T Y f (f ⁻¹ᵁ V) V le_rfl a

/-- `p₀` and `p₁` agree on sections pulled back from the base. -/
public theorem firstOrderThickeningP₁_app_of_base (V : Y.Opens) (a : Γ(Y, V)) :
    ((firstOrderThickeningP₁ T Y f).app (op (f ⁻¹ᵁ V))).hom (f.app V a) =
      ((firstOrderThickeningP₀ T Y f).app (op (f ⁻¹ᵁ V))).hom (f.app V a) :=
  sqZeroExt_ext rfl (sheafApp_app T Y f V a)

/-- **`p₀` and `p₁` are morphisms over the base `Y`, and they agree there**: their difference is
the universal divided power derivation, which kills every section pulled back from `Y`. -/
@[stacks 07J2 "p₀ and p₁ agree over the base"]
public theorem firstOrderThickeningP₁Hom_comp_base :
    firstOrderThickeningP₁Hom T Y f ≫ f = firstOrderThickeningProjHom T Y f ≫ f := by
  apply congrArg Scheme.Hom.mk
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.hext _ _ ?_ ?_
  · rfl
  · apply heq_of_eq
    ext V a
    exact firstOrderThickeningP₁_app_of_base T Y f V a

/-! ### Kernels of morphisms of sheaves of modules -/

/-- The kernel of a morphism of sheaves of modules on a scheme, as a submodule sheaf. -/
public def moduleKernelSubmodule {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N) :
    M.Submodule where
  obj U := LinearMap.ker (g.val.app U).hom
  map {U V} i := by
    intro x hx
    change (g.val.app V).hom (M.val.map i x) = 0
    rw [PresheafOfModules.naturality_apply, show (g.val.app U).hom x = 0 from hx, map_zero]
    rfl
  isSheaf {U} x hx := by
    let NN : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      ⟨N.val.presheaf, N.isSheaf⟩
    have hN' := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj NN).property
    apply (hN' _ hx).isSeparatedFor.ext
    intro V i hi
    change N.val.map i.op ((g.val.app U).hom x) = N.val.map i.op 0
    rwa [← PresheafOfModules.naturality_apply, map_zero]

/-- The submodule sheaf of kernels is a categorical kernel. -/
public def moduleKernelSubmoduleIsLimit {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N) :
    IsLimit (KernelFork.ofι (f := g) (moduleKernelSubmodule g).ι (by
      ext U x
      exact x.property)) := by
  refine Fork.IsLimit.mk _ (fun s => ?_) ?_ ?_
  · exact ⟨{
      app U := ModuleCat.ofHom ((s.ι.val.app U).hom.codRestrict
        (LinearMap.ker (g.val.app U).hom) (fun x => by
          exact congrArg (fun q => (q.val.app U).hom x) s.condition))
      naturality i := by
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply s.ι.val i x }⟩
  · intro s
    rfl
  · intro s m hm
    ext U x
    apply Subtype.ext
    exact congrArg (fun q => (q.val.app (op U)).hom x) hm

/-- The submodule sheaf of kernels agrees with the categorical kernel. -/
public def moduleKernelSubmoduleIso {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N) :
    (moduleKernelSubmodule g).toSheafOfModules ≅ kernel g :=
  (moduleKernelSubmoduleIsLimit g).conePointUniqueUpToIso (limit.isLimit _)

/-- A submodule sheaf contained in another on every affine open is contained in it. -/
public theorem submodule_le_of_affine {X : Scheme.{u}}
    (I J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (h : ∀ W : X.affineOpens, I.obj (op W.1) ≤ J.obj (op W.1)) : I ≤ J := by
  intro W s hs
  apply J.isSheaf s
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨V, homOfLE hVW, h ⟨V, hV⟩ (I.map (homOfLE hVW).op hs), hxV⟩

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S)

/-- The ideal sheaf of the immersion `U ⟶ T` of an object of `CRIS(X/S)` is the divided power
ideal of `T`: on affine opens this is part of the data of the object, and the general case
follows because both sides are submodule sheaves. -/
public theorem thickening_ideal_eq_moduleKernel :
    A.thickening.target.ideal =
      moduleKernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit A.thickening.immersion.toRingCatSheafHom) := by
  apply le_antisymm <;> apply submodule_le_of_affine <;> intro W <;>
    rw [A.thickening.ideal_eq_ker W, Scheme.Hom.ker_apply] <;> exact le_rfl

/-- **The extended ideal `J' = J ⊕ Ω_{T/S,δ}` as a sheaf of ideals on `T'`.** -/
@[stacks 07J2 "the ideal J' as a sheaf of ideals on T'"]
public def firstOrderThickeningIdealSheaf :
    (SheafOfModules.unit (firstOrderThickeningScheme A.thickening.target S.S.scheme
      A.toBase.hom).ringCatSheaf).Submodule where
  obj W := firstOrderThickeningIdeal A.thickening.target S.S.scheme A.toBase.hom
    (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
  map {_ _} i := fun _ hx => A.thickening.target.ideal.map i hx
  isSheaf {_} x hx := A.thickening.target.ideal.isSheaf (sqZeroExtFst x) hx

/-- The immersion `U ⟶ T'`: the immersion `U ⟶ T` followed by `i : T ⟶ T'`. -/
public def firstOrderThickeningSourceι :
    A.thickening.source ⟶
      firstOrderThickeningScheme A.thickening.target S.S.scheme A.toBase.hom :=
  A.thickening.immersion ≫
    firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom

/-- The immersion `U ⟶ T'` is a closed immersion, as the composite of the closed immersions
`U ⟶ T` and `T ⟶ T'`. -/
public instance firstOrderThickeningSourceι_isClosedImmersion :
    IsClosedImmersion (firstOrderThickeningSourceι S A) :=
  inferInstanceAs (IsClosedImmersion (A.thickening.immersion ≫
    firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom))

/-- The immersion `U ⟶ T'` is surjective, `U ⟶ T` and `T ⟶ T'` both being so. -/
public theorem firstOrderThickeningSourceι_surjective :
    Function.Surjective (firstOrderThickeningSourceι S A) := by
  intro z
  obtain ⟨y, hy⟩ :=
    (firstOrderThickeningι_isThickening A.thickening.target S.S.scheme A.toBase.hom).2 z
  obtain ⟨x, hx⟩ := A.thickening.isThickening.2 y
  refine ⟨x, ?_⟩
  rw [show (firstOrderThickeningSourceι S A) x =
    (firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom)
      (A.thickening.immersion x) from rfl, hx, hy]

/-- **The extended ideal is the ideal sheaf of the immersion `U ⟶ T'`**: a section `(g, ω)` of
`𝒪_{T'}` dies on `U` exactly when `g` does, because the immersion `U ⟶ T'` acts on sections
through the projection `𝒪_{T'} ⟶ 𝒪_T`. -/
public theorem firstOrderThickeningIdealSheaf_eq_moduleKernel :
    firstOrderThickeningIdealSheaf S A =
      moduleKernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit
          (firstOrderThickeningSourceι S A).toRingCatSheafHom) := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro W
  apply Submodule.ext
  intro x
  change sqZeroExtFst x ∈ A.thickening.target.ideal.obj
      (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W) ↔
    A.thickening.immersion.c.app
      (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
      (sqZeroExtFst x) = 0
  exact Iff.of_eq (congrArg
    (fun I : (SheafOfModules.unit A.thickening.target.scheme.ringCatSheaf).Submodule =>
      sqZeroExtFst x ∈ I.obj
        (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W))
    (thickening_ideal_eq_moduleKernel S A))

/-- **The extended ideal `J'` is quasi-coherent**, being the ideal sheaf of the closed immersion
`U ⟶ T'`. -/
@[stacks 07J2 "the ideal J' is quasi-coherent"]
public theorem firstOrderThickeningIdealSheaf_isQuasicoherent :
    (firstOrderThickeningIdealSheaf S A).toSheafOfModules.IsQuasicoherent := by
  rw [firstOrderThickeningIdealSheaf_eq_moduleKernel]
  exact (SheafOfModules.isQuasicoherent (firstOrderThickeningScheme A.thickening.target
    S.S.scheme A.toBase.hom).ringCatSheaf).prop_of_iso
      (moduleKernelSubmoduleIso _).symm inferInstance

/-! ### The divided power scheme `T'` and the object `(U, T', δ')` -/

/-- **The divided power scheme `(T', J', δ')`.**  The scheme `T'`, the quasi-coherent ideal
`J' = J ⊕ Ω_{T/S,δ}` and the divided power structure `δ'` of [Stacks, Tag 07J2]. -/
@[stacks 07J2 "T' with the ideal J' and the divided powers δ' is a divided power scheme"]
public abbrev firstOrderThickeningDPScheme : DividedPowerScheme.{u} where
  scheme := firstOrderThickeningScheme A.thickening.target S.S.scheme A.toBase.hom
  ideal := firstOrderThickeningIdealSheaf S A
  isQuasicoherent := firstOrderThickeningIdealSheaf_isQuasicoherent S A
  dividedPowers :=
    { dividedPowers W :=
        firstOrderThickeningDividedPowers A.thickening.target S.S.scheme A.toBase.hom
          (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)
      naturality i :=
        firstOrderThickening_restriction_isDPMorphism A.thickening.target S.S.scheme
          A.toBase.hom i }

/-- **`p₀ : T' ⟶ T` is a morphism of divided power schemes.** -/
@[stacks 07J2 "p₀ is a morphism of divided power schemes"]
public def firstOrderThickeningProjDP :
    firstOrderThickeningDPScheme S A ⟶ A.thickening.target where
  hom := firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom
  compatible W :=
    firstOrderThickeningP₀_isDPMorphism A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`p₁ : T' ⟶ T` is a morphism of divided power schemes.** -/
@[stacks 07J2 "p₁ is a morphism of divided power schemes"]
public def firstOrderThickeningP₁DP :
    firstOrderThickeningDPScheme S A ⟶ A.thickening.target where
  hom := firstOrderThickeningP₁Hom A.thickening.target S.S.scheme A.toBase.hom
  compatible W :=
    firstOrderThickeningP₁_isDPMorphism A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **`i : T ⟶ T'` is a morphism of divided power schemes.** -/
@[stacks 07J2 "i is a morphism of divided power schemes"]
public def firstOrderThickeningιDP :
    A.thickening.target ⟶ firstOrderThickeningDPScheme S A where
  hom := firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom
  compatible W :=
    firstOrderThickeningProj_isDPMorphism A.thickening.target S.S.scheme A.toBase.hom (op W)

/-- **The divided power thickening `U ⟶ T'`**: a thickening of schemes whose defining ideal is
the divided power ideal `J'`. -/
@[stacks 07J2 "U ⟶ T' is a divided power thickening"]
public abbrev firstOrderThickeningSchemeThickening : SchemeThickening.{u} where
  source := A.thickening.source
  target := firstOrderThickeningDPScheme S A
  immersion := firstOrderThickeningSourceι S A
  isThickening := ⟨firstOrderThickeningSourceι_isClosedImmersion S A,
    firstOrderThickeningSourceι_surjective S A⟩
  ideal_eq_ker V := by
    rw [Scheme.Hom.ker_apply]
    exact congrArg (fun I : (SheafOfModules.unit (firstOrderThickeningScheme
      A.thickening.target S.S.scheme A.toBase.hom).ringCatSheaf).Submodule =>
        I.obj (op V.1)) (firstOrderThickeningIdealSheaf_eq_moduleKernel S A)

/-- **`(U, T', δ')` is an object of `CRIS(X/S)`.**  This is the assertion of [Stacks, Tag 07J2]
that the first-order universal thickening of an object of the crystalline category is again an
object of it: `T'` with the ideal `J' = J ⊕ Ω_{T/S,δ}` and the divided powers `δ'` is a divided
power scheme, `U ⟶ T'` is a divided power thickening, and `T' ⟶ S` is `p₀` followed by the
structure morphism of `T`. -/
@[stacks 07J2 "(U, T', δ') is an object of CRIS(X/S)"]
public abbrev firstOrderThickeningObject : Thickening S where
  thickening := firstOrderThickeningSchemeThickening S A
  toBase := firstOrderThickeningProjDP S A ≫ A.toBase
  toX := A.toX
  over_base := by
    rw [DividedPowerScheme.Hom.comp_hom,
      show (firstOrderThickeningSchemeThickening S A).immersion =
        A.thickening.immersion ≫
          firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom =
        firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, ← Category.assoc
      (firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom),
      firstOrderThickeningι_comp_projHom, Category.id_comp]
    exact A.over_base

/-- **The morphism `i : (U, T, δ) ⟶ (U, T', δ')` of `CRIS(X/S)`.** -/
@[stacks 07J2 "the morphism i of CRIS(X/S)"]
public def firstOrderThickeningSiteι : A ⟶ firstOrderThickeningObject S A where
  sourceHom := 𝟙 _
  targetHom := firstOrderThickeningιDP S A
  immersion_naturality := by
    rw [Category.id_comp]
    rfl
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom,
      show (firstOrderThickeningιDP S A).hom =
        firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom =
        firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom from rfl,
      ← Category.assoc, firstOrderThickeningι_comp_projHom, Category.id_comp]
  toX_naturality := Category.id_comp _

/-- **The morphism `p₀ : (U, T', δ') ⟶ (U, T, δ)` of `CRIS(X/S)`.** -/
@[stacks 07J2 "the morphism p₀ of CRIS(X/S)"]
public def firstOrderThickeningSiteP₀ : firstOrderThickeningObject S A ⟶ A where
  sourceHom := 𝟙 _
  targetHom := firstOrderThickeningProjDP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (firstOrderThickeningObject S A).thickening.immersion =
        A.thickening.immersion ≫
          firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningProjDP S A).hom =
        firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, firstOrderThickeningι_comp_projHom, Category.comp_id]
  base_naturality := rfl
  toX_naturality := Category.id_comp _

/-- **The morphism `p₁ : (U, T', δ') ⟶ (U, T, δ)` of `CRIS(X/S)`.**  It is a morphism over the
divided power base because `p₁` and `p₀` agree after composing with the structure morphism of
`T`, the universal divided power derivation killing every section pulled back from `S`. -/
@[stacks 07J2 "the morphism p₁ of CRIS(X/S)"]
public def firstOrderThickeningSiteP₁ : firstOrderThickeningObject S A ⟶ A where
  sourceHom := 𝟙 _
  targetHom := firstOrderThickeningP₁DP S A
  immersion_naturality := by
    rw [Category.id_comp,
      show (firstOrderThickeningObject S A).thickening.immersion =
        A.thickening.immersion ≫
          firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningP₁DP S A).hom =
        firstOrderThickeningP₁Hom A.thickening.target S.S.scheme A.toBase.hom from rfl,
      Category.assoc, firstOrderThickeningι_comp_P₁Hom, Category.comp_id]
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    rw [DividedPowerScheme.Hom.comp_hom,
      show (firstOrderThickeningP₁DP S A).hom =
        firstOrderThickeningP₁Hom A.thickening.target S.S.scheme A.toBase.hom from rfl,
      show (firstOrderThickeningObject S A).toBase.hom =
        firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom ≫
          A.toBase.hom from rfl]
    exact firstOrderThickeningP₁Hom_comp_base A.thickening.target S.S.scheme A.toBase.hom
  toX_naturality := Category.id_comp _

/-- **`p₀ ∘ i = id` in `CRIS(X/S)`**, the left relation of the diagram of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the diagram relation p₀ ∘ i = id in CRIS(X/S)"]
public theorem firstOrderThickeningSiteι_comp_P₀ :
    firstOrderThickeningSiteι S A ≫ firstOrderThickeningSiteP₀ S A = 𝟙 A := by
  apply Thickening.Hom.ext
  · exact Category.id_comp _
  · apply DividedPowerScheme.Hom.ext
    exact firstOrderThickeningι_comp_projHom A.thickening.target S.S.scheme A.toBase.hom

/-- **`p₁ ∘ i = id` in `CRIS(X/S)`**, the right relation of the diagram of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the diagram relation p₁ ∘ i = id in CRIS(X/S)"]
public theorem firstOrderThickeningSiteι_comp_P₁ :
    firstOrderThickeningSiteι S A ≫ firstOrderThickeningSiteP₁ S A = 𝟙 A := by
  apply Thickening.Hom.ext
  · exact Category.id_comp _
  · apply DividedPowerScheme.Hom.ext
    exact firstOrderThickeningι_comp_P₁Hom A.thickening.target S.S.scheme A.toBase.hom

/-- **`i : (U, T, δ) ⟶ (U, T', δ')` is a first-order thickening whose ideal sheaf is
`Ω_{T/S,δ}`**, which is the restriction `(Ω_{X/S})_T` of the crystalline differentials by
[Stacks, Tag 07IZ]. -/
@[stacks 07J2 "i is a first-order thickening with ideal sheaf Ω_{T/S,δ}"]
public theorem firstOrderThickeningSiteι_isFirstOrderThickening :
    Stacks.Thickenings.IsFirstOrderThickening
      (firstOrderThickeningSiteι S A).targetHom.hom :=
  firstOrderThickeningι_isFirstOrderThickening A.thickening.target S.S.scheme A.toBase.hom

/-- **The ideal sheaf of `i : T ⟶ T'` is `(Ω_{X/S})_T`**, the restriction of the crystalline
differentials to the ambient scheme of the object — which is the spelling in which
[Stacks, Tag 07J2] states it.  Over every open the kernel of the map on sections of `i` is the
sheaf `Ω_{T/S,δ}` of divided power differentials, and [Stacks, Tag 07IZ] identifies that sheaf
with `(Ω_{X/S})_T`. -/
@[stacks 07J2 "the ideal sheaf of i is the restriction of Ω_{X/S} to T"]
public def firstOrderThickeningSiteKernelEquiv
    (W : (Opens ↑(firstOrderThickeningScheme A.thickening.target S.S.scheme
      A.toBase.hom))ᵒᵖ) :
    ↑((restrictedCrysDifferentialsSheaf S A).val.obj
        (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)) ≃+
      RingHom.ker (((firstOrderThickeningι A.thickening.target S.S.scheme
        A.toBase.hom).c.app W).hom) :=
  (((SheafOfModules.evaluation A.thickening.target.scheme.ringCatSheaf
        (firstOrderThickeningOpen A.thickening.target S.S.scheme A.toBase.hom W)).mapIso
      (restrictedCrysDifferentialsSheafIso S A)).toLinearEquiv.symm.toAddEquiv).trans
    (firstOrderThickeningιKernelEquiv A.thickening.target S.S.scheme A.toBase.hom W)

/-! ### The object and the diagram in the small crystalline site -/

variable (B : CrystallineThickening S)

/-- **`(U, T', δ')` is an object of the small crystalline category `Cris(X/S)`** whenever
`(U, T, δ)` is.  The construction leaves the map `U ⟶ X` untouched, so it is still an open
immersion; this is the assertion of [Stacks, Tag 07J2] in the category in which the remark
states it. -/
@[stacks 07J2 "(U, T', δ') is an object of Cris(X/S)"]
public def firstOrderThickeningCrysObject : CrystallineThickening S :=
  ⟨firstOrderThickeningObject S B.obj, B.property⟩

/-- **The morphism `i : (U, T, δ) ⟶ (U, T', δ')` of `Cris(X/S)`.** -/
@[stacks 07J2 "the morphism i of the diagram in Cris(X/S)"]
public def firstOrderThickeningCrysι : B ⟶ firstOrderThickeningCrysObject S B :=
  ObjectProperty.homMk (firstOrderThickeningSiteι S B.obj)

/-- **The morphism `p₀ : (U, T', δ') ⟶ (U, T, δ)` of `Cris(X/S)`.** -/
@[stacks 07J2 "the morphism p₀ of the diagram in Cris(X/S)"]
public def firstOrderThickeningCrysP₀ : firstOrderThickeningCrysObject S B ⟶ B :=
  ObjectProperty.homMk (firstOrderThickeningSiteP₀ S B.obj)

/-- **The morphism `p₁ : (U, T', δ') ⟶ (U, T, δ)` of `Cris(X/S)`.** -/
@[stacks 07J2 "the morphism p₁ of the diagram in Cris(X/S)"]
public def firstOrderThickeningCrysP₁ : firstOrderThickeningCrysObject S B ⟶ B :=
  ObjectProperty.homMk (firstOrderThickeningSiteP₁ S B.obj)

/-- **`p₀ ∘ i = id` in `Cris(X/S)`**, the left relation of the diagram of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the diagram relation p₀ ∘ i = id in Cris(X/S)"]
public theorem firstOrderThickeningCrysι_comp_P₀ :
    firstOrderThickeningCrysι S B ≫ firstOrderThickeningCrysP₀ S B = 𝟙 B := by
  apply ObjectProperty.hom_ext
  exact firstOrderThickeningSiteι_comp_P₀ S B.obj

/-- **`p₁ ∘ i = id` in `Cris(X/S)`**, the right relation of the diagram of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the diagram relation p₁ ∘ i = id in Cris(X/S)"]
public theorem firstOrderThickeningCrysι_comp_P₁ :
    firstOrderThickeningCrysι S B ≫ firstOrderThickeningCrysP₁ S B = 𝟙 B := by
  apply ObjectProperty.hom_ext
  exact firstOrderThickeningSiteι_comp_P₁ S B.obj

end GlobalCrystallineSituation

end Crystalline

end
