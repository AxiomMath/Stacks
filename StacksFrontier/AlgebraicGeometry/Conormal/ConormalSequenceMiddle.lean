module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Affine charts of a chain of immersions

Let `Z --i--→ Y --j--→ X` be immersions of schemes. This file collects the local material
needed to read the conormal sheaves of `i`, of `j` and of `i ≫ j` simultaneously: a notion of
*chart* for the chain, the fact that the charts of a chain cover, the affine formula of
[Stacks Project, Tag 01R4] for the left-hand map of the conormal sequence over a chart, and the
commutative-algebra exactness statement that the conormal sequence is an instance of.

## Main definitions

* `Stacks.Immersion.ConormalChart`: an affine open `V ⊆ X` with affine preimage in `Y`, over
  which all three immersions are cut out by ideals, together with the three affine models.
* `Stacks.Immersion.conormalLeftMap`: the canonical map
  `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 01R4] for the square with horizontal maps
  `i ≫ j` and `j` and vertical maps `i` and `𝟙_X`.

## Main results

* `Stacks.Conormal.exact_mapCotangent_comap`: for a surjective ring map `R ⟶ S` with kernel `J`
  and an ideal `K ⊆ S` with preimage `I ⊆ R`, the sequence `J/J² ⟶ I/I² ⟶ K/K²` is exact at
  `I/I²`.
* `Stacks.Immersion.exists_conormalChart`: every point of `Z` lies over a chart contained in a
  prescribed open of `X`.
* `Stacks.Immersion.ConormalChart.leftMap_toCotangent`: over a chart, the left-hand map of the
  conormal sequence carries the class of `k` in `K/K²` to the class of `k` in `J/J²`.
* `Stacks.Immersion.exact_of_chartwise`: a short complex of `𝒪_Z`-modules whose sections over
  the preimages of the charts are exact is exact.
* `RingedSpaceModuleAdjunction.unit_id_app`: the unit of `(𝟙)^* ⊣ (𝟙)_*` is the inverse
  of the identification of pullback along an identity with the identity functor, and
  `RingedSpaceModuleAdjunction.homEquiv_id_eq`: transposing along that adjunction is
  precomposition with that identification.

## Implementation notes

`Stacks.Immersion.iso_inv_hom_apply` and `Stacks.Immersion.iso_hom_inv_apply` record the round
trips of an isomorphism of modules on elements; injectivity of the inverse is
`Stacks.ConormalSequenceTwoImmersions.injective_iso_inv`. They are stated separately because the
isomorphisms they are used at —
the affine identifications of [Stacks Project, Tag 01R3] part (2) — have very large types, and
the round trip has to be proved once, generically, rather than unfolded at each use.

The three ideals of a chart are not parameters: they are the kernels of the maps on sections of
the three immersions over the chart, which is what makes them comparable to one another. The
affine models are parameters, because [Stacks Project, Tag 01R3] part (2) takes one.

Exactness of a complex of sheaves of modules is detected on stalks
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`), and a germ at a point
of `Z` is represented over the preimage of a chart because the charts refine any open of `X`
and every open of `Z` is the preimage of one.

## References

* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

/-! ### The conormal sequence of a quotient, on rings -/

namespace Stacks.Conormal

/-- **The conormal sequence of a surjection, on rings.** Let `R ⟶ S` be a surjective ring map
with kernel `J`, let `K ⊆ S` be an ideal and let `I ⊆ R` be its preimage. Then the sequence of
conormal modules `J/J² ⟶ I/I² ⟶ K/K²` is exact at `I/I²`: the kernel of the map induced by
`R ⟶ S` is the image of the map induced by the identity of `R`.

Since `R ⟶ S` is surjective, `I` is the extension of itself along `R ⟶ S` contracted back, so
`Ideal.mapCotangent_ker_of_surjective` computes the kernel of the second map as the image under
`I.toCotangent` of `J ⊓ I = J`; that image is exactly the range of the first map. -/
theorem exact_mapCotangent_comap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hq : Function.Surjective (algebraMap R S)) (K : Ideal S)
    (h₁ : RingHom.ker (algebraMap R S) ≤
      Ideal.comap (Algebra.ofId R R) (Ideal.comap (algebraMap R S) K))
    (h₂ : Ideal.comap (algebraMap R S) K ≤ Ideal.comap (Algebra.ofId R S) K) :
    Function.Exact
      (Ideal.mapCotangent (RingHom.ker (algebraMap R S))
        (Ideal.comap (algebraMap R S) K) (Algebra.ofId R R) h₁)
      (Ideal.mapCotangent (Ideal.comap (algebraMap R S) K) K (Algebra.ofId R S) h₂) := by
  classical
  have hJI : RingHom.ker (algebraMap R S) ≤ Ideal.comap (algebraMap R S) K := fun x hx => by
    simp [RingHom.mem_ker.mp hx]
  have hcomap : Ideal.comap (algebraMap R S) K =
      RingHom.ker (algebraMap R S) ⊔ Ideal.comap (algebraMap R S) K :=
    (sup_eq_right.mpr hJI).symm
  have key (a : R) (ha : a ∈ RingHom.ker (algebraMap R S)) :
      Ideal.mapCotangent _ _ _ h₁ (Ideal.toCotangent _ ⟨a, ha⟩) =
        Ideal.toCotangent _ ⟨a, hJI ha⟩ := by
    rw [Ideal.mapCotangent_toCotangent]
    exact congrArg _ (Subtype.ext (by simp))
  rw [LinearMap.exact_iff, Ideal.mapCotangent_ker_of_surjective hq hcomap]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    have hzJ : (z : R) ∈ RingHom.ker (algebraMap R S) :=
      (Submodule.mem_inf.mp (Submodule.mem_comap.mp hz)).1
    refine ⟨(RingHom.ker (algebraMap R S)).toCotangent ⟨(z : R), hzJ⟩, ?_⟩
    exact key _ hzJ
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := (RingHom.ker (algebraMap R S)).toCotangent_surjective y
    refine Submodule.mem_map.mpr ⟨⟨(a : R), hJI a.2⟩, ?_, ?_⟩
    · exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨a.2, hJI a.2⟩)
    · exact (key _ a.2).symm

end Stacks.Conormal

/-! ### The adjunction along an identity -/

namespace RingedSpaceModuleAdjunction

/-- **Pushforward along an identity is the identity, on morphisms.** The two functors are
definitionally equal, so this holds by `rfl`; it is stated because the two spellings are not
syntactically equal and the definitional check is expensive when the morphism is a large
term. -/
theorem modulePushforward_id_map {Zr : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Zr)} (ψ : M ⟶ N) :
    (modulePushforward (𝟙 Zr)).map ψ = ψ := rfl

/-- **The unit of `(𝟙)^* ⊣ (𝟙)_*` is the inverse of
`RingedSpaceModuleAdjunction.modulePullbackId`.** Pushforward along an identity is the
identity functor, so both sides are morphisms `M ⟶ (𝟙)^* M`.

The mate of `modulePullbackId` under the conjugation between the two adjunctions is the inverse
of `RingedSpaceModuleAdjunction.modulePushforwardId`, whose components are identities; so
the unit followed by `modulePullbackId` is the identity. -/
theorem unit_id_app (Zr : RingedSpace.{u, u}) (M : SheafOfModules.{u} (structureSheafRing Zr)) :
    (modulePullbackPushforwardAdjunction (𝟙 Zr)).unit.app M =
      (modulePullbackId Zr).inv.app M := by
  have hc : conjugateEquiv Adjunction.id (modulePullbackPushforwardAdjunction (𝟙 Zr))
      (modulePullbackId Zr).hom = (modulePushforwardId Zr).inv :=
    SheafOfModules.conjugateEquiv_pullbackId_hom (structureSheafRing Zr)
  have h := unit_conjugateEquiv (Adjunction.id (C := SheafOfModules.{u} (structureSheafRing Zr)))
    (modulePullbackPushforwardAdjunction (𝟙 Zr)) (modulePullbackId Zr).hom M
  rw [hc, modulePushforward_id_map] at h
  exact ((modulePullbackId Zr).app M).comp_hom_eq_id.mp (h.symm.trans (Category.id_comp _))

/-- **The transpose along `(𝟙)^* ⊣ (𝟙)_*` is precomposition with
`RingedSpaceModuleAdjunction.modulePullbackId`.** -/
theorem homEquiv_id_eq (Zr : RingedSpace.{u, u}) (M N : SheafOfModules.{u} (structureSheafRing Zr))
    (c : (modulePullback (𝟙 Zr)).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction (𝟙 Zr)).homEquiv M N c =
      (modulePullbackId Zr).inv.app M ≫ c := by
  rw [Adjunction.homEquiv_unit, modulePushforward_id_map, unit_id_app]
  rfl

end RingedSpaceModuleAdjunction

namespace Stacks.Immersion

variable {Z Y X : Scheme.{u}}

/-! ### Sectionwise bookkeeping -/

/-- **Restriction along an endomorphism of an open acts trivially on sections.** The only
endomorphism of an open in the category of opens is the identity. -/
theorem val_map_self_apply {Zr : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Zr)) {A : Opens Zr.carrier} (f : A ⟶ A)
    (x : M.val.obj (op A)) : M.val.map f.op x = x := by
  rw [M.val.congr_map_apply
    ((congrArg Quiver.Hom.op (Subsingleton.elim f (𝟙 A))).trans op_id) x,
    PresheafOfModules.map_id]
  rfl

/-- **A morphism of sheaves of modules vanishing on all sections is zero.** -/
theorem hom_eq_zero_of_val_app {Zr : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Zr)} (φ : M ⟶ N)
    (h : ∀ (A : Opens Zr.carrier) (x : M.val.obj (op A)), φ.val.app (op A) x = 0) : φ = 0 := by
  refine SheafOfModules.hom_ext ((PresheafOfModules.toPresheaf _).map_injective ?_)
  ext A x
  exact h A.unop x

/-- **An isomorphism of modules is undone by its inverse.** -/
theorem iso_inv_hom_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (A : M ≅ N) (x : M) :
    A.inv.hom (A.hom.hom x) = x := by
  rw [← ModuleCat.hom_comp_apply, A.hom_inv_id]
  rfl

/-- **An isomorphism of modules is undone by its inverse, the other way round.** -/
theorem iso_hom_inv_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (A : M ≅ N) (y : N) :
    A.hom.hom (A.inv.hom y) = y :=
  iso_inv_hom_apply A.symm y

/-- **Every open of the source of an immersion is the preimage of an open of the target.** An
immersion is an embedding, so its underlying map is inducing. -/
theorem exists_preimage_eq (f : Z ⟶ X) [IsImmersion f] (O : Z.Opens) :
    ∃ V : X.Opens, f ⁻¹ᵁ V = O := by
  obtain ⟨t, ht, hts⟩ := (f.isEmbedding.isInducing.isOpen_iff (s := (O : Set Z))).mp O.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext hts⟩

/-! ### Affine models over an open inside the coborder -/

/-- **An affine open inside the coborder of the range of an immersion carries an affine model.**
The scheme-theoretic intersection of the source with the open is the spectrum of a quotient of
the ring of functions on the open, compatibly with `AlgebraicGeometry.IsAffineOpen.isoSpec`,
because over such an open the immersion restricts to a closed immersion. -/
theorem exists_affineModel_of_le_coborderRange (f : Z ⟶ X) [IsImmersion f] (U : X.Opens)
    (hU : IsAffineOpen U) (hUc : U ≤ f.coborderRange) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback f U.ι ≅ Spec (quotRing I)),
      pullback.snd f U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I :=
  Stacks.Conormal.exists_affineModel_of_resLE f U hU
    (isClosedImmersion_resLE_of_le_coborderRange f U hUc)

/-- **The map on sections of an immersion over an affine open inside the coborder of its range is
surjective.** Over such an open the immersion is a closed immersion of affine schemes. -/
theorem surjective_app_of_le_coborderRange (f : Z ⟶ X) [IsImmersion f] (U : X.Opens)
    (hU : IsAffineOpen U) (hUc : U ≤ f.coborderRange) :
    Function.Surjective (f.app U).hom := by
  obtain ⟨I, e, he⟩ := exists_affineModel_of_le_coborderRange f U hU hUc
  have h := Stacks.Conormal.surjective_appLE_of_affineModel f U hU I e he
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- **The ideal of an affine model is the kernel of the map on sections.** -/
theorem ker_app_eq_of_affineModel (f : Z ⟶ X) [IsImmersion f] (U : X.Opens)
    (hU : IsAffineOpen U) (I : Ideal Γ(X, U)) (e : pullback f U.ι ≅ Spec (quotRing I))
    (he : pullback.snd f U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I) :
    RingHom.ker (f.app U).hom = I := by
  have h := Stacks.Conormal.ker_appLE_eq_of_affineModel f U hU I e he
  rwa [Scheme.Hom.appLE_eq_app] at h

/-! ### Charts of a chain of immersions -/

/-- **A chart of a chain of immersions `Z --i--→ Y --j--→ X`:** an affine open `V ⊆ X` whose
preimage in `Y` is affine, over which each of `j`, `i ≫ j` and `i` is cut out by an ideal — the
kernel of its map on sections — together with the affine models exhibiting those ideals, in the
sense of [Stacks Project, Tag 01R3] part (2). -/
structure ConormalChart (i : Z ⟶ Y) (j : Y ⟶ X) where
  /-- The affine open of the ambient scheme. -/
  V : X.Opens
  /-- `V` is affine. -/
  hV : IsAffineOpen V
  /-- The preimage of `V` in `Y` is affine. -/
  hW : IsAffineOpen (j ⁻¹ᵁ V)
  /-- The sections of `Y` over the preimage of `V` are a quotient of those of `X` over `V`. -/
  hq : Function.Surjective (j.app V).hom
  /-- The affine model of `Y ∩ V`. -/
  eY : pullback j V.ι ≅ Spec (quotRing (RingHom.ker (j.app V).hom))
  /-- Compatibility of the model of `Y ∩ V` with the affine identification of `V`. -/
  heY : pullback.snd j V.ι ≫ hV.isoSpec.hom =
    eY.hom ≫ quotImmersion Γ(X, V) (RingHom.ker (j.app V).hom)
  /-- The affine model of `Z ∩ V`. -/
  eZ : pullback (i ≫ j) V.ι ≅ Spec (quotRing (RingHom.ker ((i ≫ j).app V).hom))
  /-- Compatibility of the model of `Z ∩ V` with the affine identification of `V`. -/
  heZ : pullback.snd (i ≫ j) V.ι ≫ hV.isoSpec.hom =
    eZ.hom ≫ quotImmersion Γ(X, V) (RingHom.ker ((i ≫ j).app V).hom)
  /-- The affine model of `Z ∩ V` inside the preimage of `V` in `Y`. -/
  eI : pullback i (j ⁻¹ᵁ V).ι ≅ Spec (quotRing (RingHom.ker (i.app (j ⁻¹ᵁ V)).hom))
  /-- Compatibility of that model with the affine identification of the preimage of `V`. -/
  heI : pullback.snd i (j ⁻¹ᵁ V).ι ≫ hW.isoSpec.hom =
    eI.hom ≫ quotImmersion Γ(Y, j ⁻¹ᵁ V) (RingHom.ker (i.app (j ⁻¹ᵁ V)).hom)

namespace ConormalChart

variable {i : Z ⟶ Y} {j : Y ⟶ X}

/-- The ideal cutting out `Y` in the chart. -/
abbrev idealY (C : ConormalChart i j) : Ideal Γ(X, C.V) := RingHom.ker (j.app C.V).hom

/-- The ideal cutting out `Z` in the chart. -/
abbrev idealZ (C : ConormalChart i j) : Ideal Γ(X, C.V) := RingHom.ker ((i ≫ j).app C.V).hom

/-- The ideal cutting out `Z` in the preimage of the chart in `Y`. -/
abbrev idealZY (C : ConormalChart i j) : Ideal Γ(Y, j ⁻¹ᵁ C.V) :=
  RingHom.ker (i.app (j ⁻¹ᵁ C.V)).hom

/-- A function vanishing on `Y ∩ V` vanishes on `Z ∩ V`. -/
theorem idealY_le_idealZ (C : ConormalChart i j) : C.idealY ≤ C.idealZ := by
  intro x hx
  have hx0 : (j.app C.V).hom x = 0 := hx
  have : (i.app (j ⁻¹ᵁ C.V)).hom ((j.app C.V).hom x) = 0 := by rw [hx0, map_zero]
  exact this

/-- The restriction to `Y ∩ V` of a function vanishing on `Z ∩ V` vanishes on `Z ∩ V`. -/
theorem map_mem_idealZY (C : ConormalChart i j) (c : C.idealZ) :
    (j.app C.V).hom (c : Γ(X, C.V)) ∈ C.idealZY := c.2

/-- The identification of [Stacks Project, Tag 01R3] part (2) of the conormal sections of `j`
over the chart with `K/K²`. -/
abbrev isoY (C : ConormalChart i j) [IsImmersion j] :=
  Stacks.Conormal.affineConormalIsoCotangent j C.V C.hV C.idealY C.eY C.heY

/-- The identification of [Stacks Project, Tag 01R3] part (2) of the conormal sections of
`i ≫ j` over the chart with `J/J²`. -/
abbrev isoZ (C : ConormalChart i j) [IsImmersion i] [IsImmersion j] :=
  Stacks.Conormal.affineConormalIsoCotangent (i ≫ j) C.V C.hV C.idealZ C.eZ C.heZ

/-- The identification of [Stacks Project, Tag 01R3] part (2) of the conormal sections of `i`
over the preimage of the chart with `I/I²`. -/
abbrev isoZY (C : ConormalChart i j) [IsImmersion i] :=
  Stacks.Conormal.affineConormalIsoCotangent i (j ⁻¹ᵁ C.V) C.hW C.idealZY C.eI C.heI

end ConormalChart

/-- **Every point of `Z` lies over a chart contained in a prescribed open of `X`.** -/
theorem exists_conormalChart (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (z : Z) (V₀ : X.Opens) (hz : (i ≫ j) z ∈ V₀) :
    ∃ C : ConormalChart i j, C.V ≤ V₀ ∧ z ∈ (i ≫ j) ⁻¹ᵁ C.V := by
  classical
  obtain ⟨V₁, hV₁⟩ := exists_preimage_eq j i.coborderRange
  have h1 : (i ≫ j) z ∈ V₁ := by
    have h : i z ∈ j ⁻¹ᵁ V₁ := by rw [hV₁]; exact subset_coborder ⟨z, rfl⟩
    exact h
  have hmem : (i ≫ j) z ∈ V₀ ⊓ V₁ ⊓ j.coborderRange ⊓ (i ≫ j).coborderRange :=
    ⟨⟨⟨hz, h1⟩, subset_coborder ⟨i z, rfl⟩⟩, subset_coborder ⟨z, rfl⟩⟩
  obtain ⟨V, hVa, hzV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hmem
  have hVa' : IsAffineOpen V := hVa
  have hVj : V ≤ j.coborderRange := hVle.trans (inf_le_left.trans inf_le_right)
  have hVij : V ≤ (i ≫ j).coborderRange := hVle.trans inf_le_right
  have hVV₁ : V ≤ V₁ := hVle.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  obtain ⟨K, eY, heY⟩ := exists_affineModel_of_le_coborderRange j V hVa' hVj
  obtain ⟨J, eZ, heZ⟩ := exists_affineModel_of_le_coborderRange (i ≫ j) V hVa' hVij
  have hW : IsAffineOpen (j ⁻¹ᵁ V) := Stacks.Conormal.isAffineOpen_preimage_of_affineModel j V K eY
  have hWc : j ⁻¹ᵁ V ≤ i.coborderRange := by
    rw [← hV₁]
    exact j.preimage_mono hVV₁
  obtain ⟨I, eI, heI⟩ := exists_affineModel_of_le_coborderRange i (j ⁻¹ᵁ V) hW hWc
  obtain rfl := ker_app_eq_of_affineModel j V hVa' K eY heY
  obtain rfl := ker_app_eq_of_affineModel (i ≫ j) V hVa' J eZ heZ
  obtain rfl := ker_app_eq_of_affineModel i (j ⁻¹ᵁ V) hW I eI heI
  exact ⟨{ V := V, hV := hVa', hW := hW
           hq := surjective_app_of_le_coborderRange j V hVa' hVj
           eY := eY, heY := heY, eZ := eZ, heZ := heZ, eI := eI, heI := heI },
    hVle.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hzV⟩

/-! ### The left-hand map of the conormal sequence -/

/-- **The left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of
[Stacks Project, Tag 062S].** It is the canonical map of [Stacks Project, Tag 01R4] attached to
the square with horizontal maps `i ≫ j` and `j` and vertical maps `i` and `𝟙_X`. -/
def conormalLeftMap (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (modulePullback i.toLRSHom.toShHom).obj (conormalSheaf j.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom :=
  immersionConormalSheafMap (i ≫ j) j i (𝟙 X)
    (toShHom_square (by rw [Category.comp_id]))

/-- **The left-hand map on an affine generator.** Over a chart, the transpose along
`i^* ⊣ i_*` of `Stacks.Immersion.conormalLeftMap` carries the class in `K/K²` of a
function `k` cutting out `Y` to the class in `J/J²` of the same function, now read as cutting
out `Z`.

This is the affine characterisation of [Stacks Project, Tag 01R4] at the pair of affine opens
`V ⊆ X` and `V ⊆ X` for the square whose right edge is the identity of `X`. -/
theorem ConormalChart.leftMap_toCotangent {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i]
    [IsImmersion j] (C : ConormalChart i j) (k : C.idealY) :
    ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
          (conormalLeftMap i j)).val.app (op (j ⁻¹ᵁ C.V))
        (C.isoY.inv.hom (C.idealY.toCotangent k)) =
      C.isoZ.inv.hom
        (C.idealZ.toCotangent ⟨(k : Γ(X, C.V)), C.idealY_le_idealZ k.2⟩) := by
  have hId : Scheme.Hom.appLE (𝟙 X) C.V C.V (by simp) = 𝟙 Γ(X, C.V) := by
    have e : C.V ≤ (𝟙 X) ⁻¹ᵁ C.V := by simp
    show Scheme.Hom.app (𝟙 X) C.V ≫ X.presheaf.map (homOfLE e).op = _
    rw [Scheme.Hom.id_app]
    show 𝟙 Γ(X, C.V) ≫ X.presheaf.map (𝟙 C.V).op = _
    simp
  have h := isInducedConormalSheafMap_immersionConormalSheafMap (i ≫ j) j i (𝟙 X)
    (show (i ≫ j) ≫ 𝟙 X = i ≫ j by rw [Category.comp_id])
    C.V C.hV C.V C.hV (by simp) C.idealZ C.idealY C.eZ C.heZ C.eY C.heY k
    ⟨(k : Γ(X, C.V)), C.idealY_le_idealZ k.2⟩ (by rw [hId]; rfl)
  exact (val_map_self_apply (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom) _ _).symm.trans h

/-- **The left-hand map on an affine generator, through the adjunction unit.** This is
`Stacks.Immersion.ConormalChart.leftMap_toCotangent` with the transpose written out as the unit
of `i^* ⊣ i_*` followed by the map, which is the form in which the generator is produced. -/
theorem ConormalChart.leftMap_unit_toCotangent {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i]
    [IsImmersion j] (C : ConormalChart i j) (k : C.idealY) :
    (conormalLeftMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ C.V))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
            (conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app (op (j ⁻¹ᵁ C.V))
          (C.isoY.inv.hom (C.idealY.toCotangent k))) =
      C.isoZ.inv.hom
        (C.idealZ.toCotangent ⟨(k : Γ(X, C.V)), C.idealY_le_idealZ k.2⟩) := by
  have h := C.leftMap_toCotangent k
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-! ### Exactness from exactness over the charts -/

/-- **A short complex of `𝒪_Z`-modules exact over the preimage of every chart is exact.**
Exactness is detected on stalks, and every germ at a point of `Z` is represented by a section
over the preimage of a chart, because every open of `Z` is the preimage of an open of `X` and
the charts refine any open of `X`. -/
theorem exact_of_chartwise (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (S : ShortComplex
      (SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)))
    (hS : ∀ (C : ConormalChart i j) (β : S.X₂.val.obj (op ((i ≫ j) ⁻¹ᵁ C.V))),
      S.g.val.app (op ((i ≫ j) ⁻¹ᵁ C.V)) β = 0 →
      ∃ α, S.f.val.app (op ((i ≫ j) ⁻¹ᵁ C.V)) α = β) :
    S.Exact := by
  classical
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) S).mpr fun z => ?_
  refine (ShortComplex.ab_exact_iff_function_exact _).2 fun m => ?_
  constructor
  · intro hm
    obtain ⟨O₁, hzO₁, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq S.X₂.val.presheaf (x := z) m
    have hgm : TopCat.Presheaf.germ S.X₃.val.presheaf O₁ z hzO₁
        (S.g.val.app (op O₁) s) = 0 := by
      refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := S.X₂.val.presheaf)
        (G := S.X₃.val.presheaf) O₁ z hzO₁
        ((PresheafOfModules.toPresheaf _).map S.g.val) s).symm.trans ?_
      rwa [hs]
    obtain ⟨W, hzW, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq S.X₃.val.presheaf z hzO₁ hzO₁
      (S.g.val.app (op O₁) s) 0 (by rw [hgm, map_zero])
    obtain ⟨V₀, hV₀⟩ := exists_preimage_eq (i ≫ j) W
    have hzV₀ : (i ≫ j) z ∈ V₀ := (show z ∈ (i ≫ j) ⁻¹ᵁ V₀ by rwa [hV₀])
    obtain ⟨C, hCV, hCz⟩ := exists_conormalChart i j z V₀ hzV₀
    have hCW : (i ≫ j) ⁻¹ᵁ C.V ≤ W := by
      rw [← hV₀]
      exact (i ≫ j).preimage_mono hCV
    have hCO : (i ≫ j) ⁻¹ᵁ C.V ≤ O₁ := hCW.trans iU.le
    have h2 : S.X₃.val.map iU.op (S.g.val.app (op O₁) s) = 0 :=
      (show S.X₃.val.map iU.op (S.g.val.app (op O₁) s) =
        S.X₃.val.map iV.op (0 : S.X₃.val.obj (op O₁)) from hWeq).trans (map_zero _)
    have hgβ : S.g.val.app (op ((i ≫ j) ⁻¹ᵁ C.V))
        (S.X₂.val.map (homOfLE hCO).op s) = 0 := by
      refine (PresheafOfModules.naturality_apply S.g.val (homOfLE hCO).op s).trans ?_
      refine (PresheafOfModules.map_comp_apply S.X₃.val iU.op (homOfLE hCW).op
        (S.g.val.app (op O₁) s)).trans ?_
      rw [h2]
      exact map_zero _
    obtain ⟨α, hα⟩ := hS C (S.X₂.val.map (homOfLE hCO).op s) hgβ
    refine ⟨TopCat.Presheaf.germ S.X₁.val.presheaf ((i ≫ j) ⁻¹ᵁ C.V) z hCz α, ?_⟩
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := S.X₁.val.presheaf)
      (G := S.X₂.val.presheaf) ((i ≫ j) ⁻¹ᵁ C.V) z hCz
      ((PresheafOfModules.toPresheaf _).map S.f.val) α).trans ?_
    refine Eq.trans (congrArg
      (fun w => TopCat.Presheaf.germ S.X₂.val.presheaf ((i ≫ j) ⁻¹ᵁ C.V) z hCz w) hα) ?_
    exact (TopCat.Presheaf.germ_res_apply' S.X₂.val.presheaf (homOfLE hCO).op z hCz s).trans hs
  · rintro ⟨n, rfl⟩
    simp

end Stacks.Immersion

end
