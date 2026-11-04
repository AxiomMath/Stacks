module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Stein factorization commutes with flat base change

Let `f : X ⟶ Y` be a universally closed and quasi-separated morphism of algebraic spaces over
`S`, and `X ⟶ Y' ⟶ Y` its factorization through the normalization of `Y` in `X`
(`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs` proves its five clauses).  The
closing sentence of Stacks 0A19 says that formation of this factorization commutes with flat base
change.  This file proves it, and states Stacks 0A19 in full.

## Main results

* `AlgebraicGeometry.Space.isIso_fSharp_of_isPullback_of_isFlat`: for a cartesian square with
  `h : X ⟶ T` quasi-compact and quasi-separated and `g : T' ⟶ T` flat, if `𝒪_T ⟶ h_* 𝒪_X` is an
  isomorphism then so is `𝒪_{T'} ⟶ h'_* 𝒪_{X'}`.
* `AlgebraicGeometry.Space.existsUnique_iso_normalizationInQcqs_of_isPullback_of_isFlat`: the base
  change along a flat `Y₁ ⟶ Y` of the Stein factorization of `f` is the Stein factorization of the
  base change of `f`.
* `AlgebraicGeometry.Space.steinFactorization_of_universallyClosed`: **Stacks 0A19**, all five
  clauses and the compatibility with flat base change.

## Implementation notes

**Flat base change of `f'_* 𝒪_X = 𝒪_{Y'}`.**  The degree-zero flat base change theorem for
quasi-coherent modules, `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`
(Stacks 073K, part (1), degree zero), applied to `𝒪_X` gives an isomorphism of `𝒪_{T'}`-modules
`h'_* 𝒪_{X'} ≅ g^* h_* 𝒪_X ≅ g^* 𝒪_T ≅ 𝒪_{T'}`.  Rather than identify this composite with the
structure map, which would need the base change map to be compatible with unit sections and
with the identifications `g^* 𝒪 ≅ 𝒪`, the proof uses only that *some* module isomorphism exists:
a commutative `R`-algebra `A` with `A ≅ R` as `R`-modules has bijective structure map
(`Algebra.bijective_algebraMap_of_bijective_smul`; if `1 = a e` and `e² = b e` for the generator
`e`, then `ab = 1`).  Applied on every chart to the algebra `h'_* 𝒪_{X'}` this makes its structure
map an isomorphism.

**From there to the factorization.**  With `P = Y₁ ×_Y Y'` and `h : X₁ ⟶ P` the base change of
`f'`, the square `X₁ ⟶ X` over `P ⟶ Y'` is cartesian and `P ⟶ Y'` is flat, so `𝒪_P ≅ h_* 𝒪_{X₁}`.
Pushing forward along the affine `P ⟶ Y₁` gives `p_* 𝒪_P ≅ f_{1,*} 𝒪_{X₁}`, and the second
assertion of Stacks 0A0Q for the universally closed `f₁`
(`AlgebraicGeometry.Space.existsUnique_iso_normalizationInQcqs_of_universallyClosed`) identifies
`P` with the normalization of `Y₁` in `X₁`.

## References

* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- A ring `M` which is an `R`-algebra and in which `r ↦ r • e` is bijective for some `e` has
bijective structure map: writing `1 = u • e` and `e * e = v • e`, injectivity gives `u * v = 1`,
so `e = v • 1` and `r • e = (r * v) • 1`. -/
theorem Algebra.bijective_algebraMap_of_bijective_smul {R M : Type*} [CommRing R]
    [CommRing M] [Algebra R M] (e : M) (h : Function.Bijective fun r : R => r • e) :
    Function.Bijective (algebraMap R M) := by
  obtain ⟨a, ha⟩ := h.2 1
  obtain ⟨b, hb⟩ := h.2 (e * e)
  simp only at ha hb
  have hab : a * b = 1 := by
    refine h.1 ?_
    simp only
    rw [one_smul, mul_smul, hb, ← smul_mul_assoc, ha, one_mul]
  have he : e = algebraMap R M b := by
    rw [Algebra.algebraMap_eq_smul_one, ← ha, smul_smul, mul_comm, hab, one_smul]
  refine ⟨fun r s hrs => h.1 ?_, fun x => ?_⟩
  · simp only
    rw [he, Algebra.smul_def, Algebra.smul_def, hrs]
  · obtain ⟨c, rfl⟩ := h.2 x
    exact ⟨c * b, by simp only; rw [he, Algebra.smul_def, map_mul]⟩

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **An algebra sheaf whose underlying module is free of rank one has bijective structure
maps.**  If the `𝒪_F`-module underlying an algebra sheaf `A` is isomorphic to `𝒪_F`, then on every
chart the structure-algebra map `𝒪_F(U) ⟶ A(U)` is bijective: the isomorphism is
`r ↦ r • e` for `e` the image of `1`, and
`Algebra.bijective_algebraMap_of_bijective_smul` applies.  The isomorphism need not be the
structure map itself. -/
theorem bijective_algebraMap_of_iso_unit (A : AlgebraSheaf.{u, u} B S hS F hF)
    (c : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ≅
      A.underlyingModule) (U : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Bijective (A.algebraMap U) := by
  let : Algebra ((structureSheaf B S hS F hF).obj.obj U) (A.right.obj.obj U) :=
    (A.algebraMap U).toAlgebra
  let φ := (c.hom.val.app U).hom
  have hφ : Function.Bijective φ := by
    have h1 : ∀ x, (c.inv.val.app U).hom (φ x) = x := fun x =>
      congrArg (fun m => (m.val.app U).hom x) c.hom_inv_id
    have h2 : ∀ y, φ ((c.inv.val.app U).hom y) = y := fun y =>
      congrArg (fun m => (m.val.app U).hom y) c.inv_hom_id
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩
  let one : ↑((SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).val.obj U) :=
    (1 : (structureSheaf B S hS F hF).obj.obj U)
  let ψ : (structureSheaf B S hS F hF).obj.obj U → A.right.obj.obj U := fun r => φ r
  let e : A.right.obj.obj U := φ one
  refine Algebra.bijective_algebraMap_of_bijective_smul e ?_
  have hfun : (fun r : (structureSheaf B S hS F hF).obj.obj U => r • e) = ψ :=
    funext fun r => (φ.map_smul r one).symm.trans (congrArg φ (mul_one r))
  rw [hfun]
  exact hφ

end AlgebraSheaf

/-! ### The structure map of a morphism and its direct image of the structure sheaf -/

section StructureMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {X T : AlgebraicSpaces B S hS}

/-- If the structure map `𝒪_T ⟶ h_* 𝒪_X` of `h : X ⟶ T` (Stacks 03G8) is an isomorphism, then the
direct image `h_* 𝒪_X` is, as an `𝒪_T`-module, isomorphic to `𝒪_T`: the structure map is an
isomorphism of algebra sheaves from `𝒪_T` to `h_* 𝒪_X`, and the module underlying `h_* 𝒪_X` is
the direct image of `𝒪_X` (`AlgebraicGeometry.Space.underlyingModule_pushforwardAlgebra`). -/
noncomputable def unitIsoModulePushforwardOfIsIsoFSharp (h : X ⟶ T)
    [IsIso (smallEtaleRingedToposHom B S hS h).fSharp] :
    SheafOfModules.unit (structureRingSheaf B S hS T) ≅
      (modulePushforward B S hS h).obj (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  haveI : IsIso (unitAlgebraHom B S hS T (pushforwardAlgebra B S hS (Over.mk h))).right :=
    inferInstanceAs (IsIso (smallEtaleRingedToposHom B S hS h).fSharp)
  AlgebraSheaf.underlyingModuleFunctor.mapIso
      (AlgebraSheaf.isoOfIsIsoRight
        (unitAlgebraHom B S hS T (pushforwardAlgebra B S hS (Over.mk h)))) ≪≫
    eqToIso (underlyingModule_pushforwardAlgebra B S hS h)

/-- **Conversely, if `h_* 𝒪_X` is isomorphic to `𝒪_T` as an `𝒪_T`-module, by any isomorphism,
then the structure map `𝒪_T ⟶ h_* 𝒪_X` is an isomorphism.**  On every chart `h_* 𝒪_X` is a ring
which is free of rank one over `𝒪_T`, so its structure map is bijective
(`AlgebraicGeometry.Space.AlgebraSheaf.bijective_algebraMap_of_iso_unit`). -/
theorem isIso_fSharp_of_iso_unit (h : X ⟶ T)
    (c : SheafOfModules.unit (structureRingSheaf B S hS T) ≅
      (modulePushforward B S hS h).obj (SheafOfModules.unit (structureRingSheaf B S hS X))) :
    IsIso (smallEtaleRingedToposHom B S hS h).fSharp :=
  isIso_commRingSheafHom_of_bijective_app _ fun U =>
    AlgebraSheaf.bijective_algebraMap_of_iso_unit (pushforwardAlgebra B S hS (Over.mk h))
      (c ≪≫ eqToIso (underlyingModule_pushforwardAlgebra B S hS h).symm) U

/-- **The condition `h_* 𝒪_X = 𝒪_T` is preserved by flat base change.**  Let

```
X' --g'--> X
|h'        |h
T' --g-->  T
```

be a cartesian square of algebraic spaces with `h` quasi-compact and quasi-separated and `g`
flat.  If the structure map `𝒪_T ⟶ h_* 𝒪_X` is an isomorphism, so is `𝒪_{T'} ⟶ h'_* 𝒪_{X'}`.

By flat base change in degree zero (Stacks 073K, part (1), for the quasi-coherent module `𝒪_X`)
`g^* h_* 𝒪_X ≅ h'_* g'^* 𝒪_X`, and inverse images of structure sheaves are structure sheaves, so
`h'_* 𝒪_{X'} ≅ g^* h_* 𝒪_X ≅ g^* 𝒪_T ≅ 𝒪_{T'}` as `𝒪_{T'}`-modules; an algebra sheaf free of rank
one as a module has invertible structure map. -/
theorem isIso_fSharp_of_isPullback_of_isFlat {X T X' T' : AlgebraicSpaces B S hS} {h : X ⟶ T}
    {g : T' ⟶ T} {h' : X' ⟶ T'} {g' : X' ⟶ X} (sq : IsPullback g' h' h g)
    (hqc : IsQuasiCompact B S hS h.hom) (hqs : IsQuasiSeparated B S hS h.hom)
    (hg : IsFlat B S hS g.hom) [IsIso (smallEtaleRingedToposHom B S hS h).fSharp] :
    IsIso (smallEtaleRingedToposHom B S hS h').fSharp := by
  have hbc := isIso_moduleBaseChangeMap_app_of_isFlat sq hqc hqs hg
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  exact isIso_fSharp_of_iso_unit h'
    ((modulePullbackUnitIso B S hS g).symm ≪≫
      (modulePullback B S hS g).mapIso (unitIsoModulePushforwardOfIsIsoFSharp h) ≪≫
      @asIso _ _ _ _ _ hbc ≪≫
      (modulePushforward B S hS h').mapIso (modulePullbackUnitIso B S hS g'))

end StructureMap

/-! ### The Stein factorization commutes with flat base change -/

section FlatBaseChange

/-- The base change of a universally closed morphism of algebraic spaces is universally closed. -/
private theorem universallyClosed_of_isPullback_of_universallyClosed
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y X₁ Y₁ : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y₁ ⟶ Y} {f₁ : X₁ ⟶ Y₁} {g' : X₁ ⟶ X}
    (sq : IsPullback g' f₁ f g) (huc : UniversallyClosed B S hS f.hom) :
    UniversallyClosed B S hS f₁.hom :=
  universallyClosed_of_isPullback B S hS X₁.2 X.2 Y₁.2 Y.2 f.hom g.hom huc
    (sq.map (ObjectProperty.ι _)).flip

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **The Stein factorization of a universally closed morphism commutes with flat base change.**
Let `f : X ⟶ Y` be universally closed, quasi-compact and quasi-separated, with Stein
factorization `X ⟶ Y' ⟶ Y` (Stacks 0822), let `g : Y₁ ⟶ Y` be flat, `X₁ = Y₁ ×_Y X` with
`f₁ : X₁ ⟶ Y₁`, and let `P = Y₁ ×_Y Y'` with `p : P ⟶ Y₁`, `q : P ⟶ Y'`, and `h : X₁ ⟶ P` the base
change of `f'`.  Then the factorization `X₁ ⟶ P ⟶ Y₁` is the Stein factorization of `f₁`: the
normalization of `Y₁` in `X₁` is identified with `P` by a unique isomorphism carrying `f'₁` to `h`
and `ν₁` to `p`. -/
theorem existsUnique_iso_normalizationInQcqs_of_isPullback_of_isFlat
    (huc : UniversallyClosed B S hS f.hom) {X₁ Y₁ P : AlgebraicSpaces B S hS} {g : Y₁ ⟶ Y}
    {f₁ : X₁ ⟶ Y₁} {g' : X₁ ⟶ X} (sq : IsPullback g' f₁ f g) (hg : IsFlat B S hS g.hom)
    {q : P ⟶ normalizationInQcqs B S hS f hfqc hfqs} {p : P ⟶ Y₁}
    (sqP : IsPullback q p (normalizationInQcqsHom B S hS f hfqc hfqs) g) (h : X₁ ⟶ P)
    (hq : h ≫ q = g' ≫ toNormalizationInQcqs f hfqc hfqs) (hp : h ≫ p = f₁)
    (hf₁qc : IsQuasiCompact B S hS f₁.hom) (hf₁qs : IsQuasiSeparated B S hS f₁.hom) :
    ∃! e : normalizationInQcqs B S hS f₁ hf₁qc hf₁qs ≅ P,
      toNormalizationInQcqs f₁ hf₁qc hf₁qs ≫ e.hom = h ∧
        e.hom ≫ p = normalizationInQcqsHom B S hS f₁ hf₁qc hf₁qs := by
  set f' := toNormalizationInQcqs f hfqc hfqs
  set ν := normalizationInQcqsHom B S hS f hfqc hfqs
  have sqPι : IsPullback q.hom p.hom ν.hom g.hom := sqP.map (ObjectProperty.ι _)
  have huc₁ := universallyClosed_of_isPullback_of_universallyClosed sq huc
  -- the square over `f'` is cartesian
  have hbig : IsPullback g' (h ≫ p) (f' ≫ ν) g := by
    rw [hp, toNormalizationInQcqs_comp]
    exact sq
  have htop : IsPullback g' h f' q := IsPullback.of_bot hbig hq.symm sqP
  have hqflat : IsFlat B S hS q.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sqP.flip hg
  have := isIso_fSharp_toNormalizationInQcqs f hfqc hfqs huc
  have : IsIso (smallEtaleRingedToposHom B S hS h).fSharp :=
    isIso_fSharp_of_isPullback_of_isFlat htop
      (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
      (isQuasiSeparated_toNormalizationInQcqs f hfqc hfqs) hqflat
  -- `P` is affine over `Y₁`, and `h` induces an isomorphism of direct-image algebras
  let Z : AffineOver B S hS Y₁ :=
    ⟨Over.mk p, isAffineHom_of_isPullback' B S hS sqPι
      (isAffineHom_normalizationInQcqsHom B S hS f hfqc hfqs)⟩
  let hZ : Over.mk f₁ ⟶ Z.obj := Over.homMk h hp
  have : IsIso (pushforwardAlgebraMap B S hS hZ).right :=
    isIso_pushforwardRingMap B S hS hZ (inferInstanceAs
      (IsIso (smallEtaleRingedToposHom B S hS h).fSharp))
  have : IsIso (pushforwardAlgebraMap B S hS hZ) :=
    (AlgebraSheaf.isoOfIsIsoRight (pushforwardAlgebraMap B S hS hZ)).isIso_hom
  obtain ⟨k, hk, hkuniq⟩ :=
    existsUnique_iso_normalizationInQcqs_of_universallyClosed f₁ hf₁qc hf₁qs huc₁ Z hZ
  refine ⟨(Over.forget _).mapIso k, ⟨congrArg CommaMorphism.left hk, Over.w k.hom⟩, ?_⟩
  rintro e ⟨he1, he2⟩
  let eo : (normalizationInQcqsAffineOver B S hS f₁ hf₁qc hf₁qs).obj ≅ Z.obj :=
    Over.isoMk e he2
  have : eo = k := hkuniq eo (Over.OverMorphism.ext he1)
  ext1
  exact congrArg (fun m => m.hom.left) this

end FlatBaseChange

/-! ### Stacks 0A19 -/

section Stein

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Stacks 0A19 (Stein factorization).**  Let `f : X ⟶ Y` be a universally closed and
quasi-separated morphism of algebraic spaces over `S`.  It is quasi-compact (Stacks 04XW); let
`Y'` be the normalization of `Y` in `X` (Stacks 0822), with `π : Y' ⟶ Y` and the canonical
`f' : X ⟶ Y'`.  Then `f = π ∘ f'`, and

1. `f'` is universally closed, quasi-compact, quasi-separated and surjective;
2. `π` is integral;
3. `f'_* 𝒪_X = 𝒪_{Y'}`: the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` is an isomorphism;
4. `Y' = \underline{Spec}_Y(f_* 𝒪_X)`: `π` is affine and the map `π_* 𝒪_{Y'} ⟶ f_* 𝒪_X` of
   `𝒪_Y`-algebras induced by `f'` is an isomorphism;
5. `Y'` is the normalization of `Y` in `X`, here in the characterizing form of Stacks 0823 (it is
   that normalization by construction).

Moreover formation of the factorization commutes with flat base change: for a flat `g : Y₁ ⟶ Y`,
a fibre product `X₁ = Y₁ ×_Y X` with `f₁ : X₁ ⟶ Y₁`, a fibre product `P = Y₁ ×_Y Y'` with
`p : P ⟶ Y₁`, and the base change `h : X₁ ⟶ P` of `f'`, the morphism `f₁` is again universally
closed and quasi-separated (so quasi-compact), the factorization `X₁ ⟶ P ⟶ Y₁` is the normalization
of `Y₁` in `X₁` in the sense of Stacks 0823, and it is identified with the factorization of `f₁`
through its own normalization by a unique isomorphism compatible with both factorizations. -/
@[stacks 0A19 "all five clauses and the compatibility with flat base change, for the \
factorization through the normalization of Stacks 0822",
  ega "III 4.3.4" "more general",
  ega "III 7.8.10" "partial"]
theorem steinFactorization_of_universallyClosed (huc : UniversallyClosed B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    let hfqc := isQuasiCompact_of_universallyClosed B S hS X.2 Y.2 f.hom huc
    toNormalizationInQcqs f hfqc hfqs ≫ normalizationInQcqsHom B S hS f hfqc hfqs = f ∧
      (UniversallyClosed B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
        IsQuasiCompact B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
        IsQuasiSeparated B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
        IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom) ∧
      IsIntegralHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
      IsIso (smallEtaleRingedToposHom B S hS (toNormalizationInQcqs f hfqc hfqs)).fSharp ∧
      (IsAffineHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
        IsIso (pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs))) ∧
      IsRelativeNormalization B S hS f.hom (normalizationInQcqsHom B S hS f hfqc hfqs).hom
        (toNormalizationInQcqs f hfqc hfqs).hom ∧
      ∀ {X₁ Y₁ P : AlgebraicSpaces B S hS} {g : Y₁ ⟶ Y} {f₁ : X₁ ⟶ Y₁} {g' : X₁ ⟶ X},
        IsPullback g' f₁ f g → IsFlat B S hS g.hom →
        ∀ {q : P ⟶ normalizationInQcqs B S hS f hfqc hfqs} {p : P ⟶ Y₁},
          IsPullback q p (normalizationInQcqsHom B S hS f hfqc hfqs) g →
          ∀ h : X₁ ⟶ P, h ≫ q = g' ≫ toNormalizationInQcqs f hfqc hfqs → h ≫ p = f₁ →
            UniversallyClosed B S hS f₁.hom ∧
              ∃ (hf₁qc : IsQuasiCompact B S hS f₁.hom) (hf₁qs : IsQuasiSeparated B S hS f₁.hom),
                IsRelativeNormalization B S hS f₁.hom p.hom h.hom ∧
                  ∃! e : normalizationInQcqs B S hS f₁ hf₁qc hf₁qs ≅ P,
                    toNormalizationInQcqs f₁ hf₁qc hf₁qs ≫ e.hom = h ∧
                      e.hom ≫ p = normalizationInQcqsHom B S hS f₁ hf₁qc hf₁qs := by
  intro hfqc
  refine ⟨toNormalizationInQcqs_comp f hfqc hfqs,
    ⟨universallyClosed_toNormalizationInQcqs B S hS f hfqc hfqs huc,
      isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs,
      isQuasiSeparated_toNormalizationInQcqs f hfqc hfqs,
      isSurjective_toNormalizationInQcqs B S hS f hfqc hfqs huc⟩,
    isIntegralHom_normalizationInQcqsHom f hfqc hfqs,
    isIso_fSharp_toNormalizationInQcqs f hfqc hfqs huc,
    ⟨isAffineHom_normalizationInQcqsHom B S hS f hfqc hfqs,
      isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed f hfqc hfqs huc⟩,
    isRelativeNormalization_normalizationInQcqs f hfqc hfqs, ?_⟩
  intro X₁ Y₁ P g f₁ g' sq hg q p sqP h hq hp
  have sqι : IsPullback g'.hom f₁.hom f.hom g.hom := sq.map (ObjectProperty.ι _)
  have huc₁ := universallyClosed_of_isPullback_of_universallyClosed sq huc
  have hf₁qc : IsQuasiCompact B S hS f₁.hom :=
    isQuasiCompact_of_universallyClosed B S hS X₁.2 Y₁.2 f₁.hom huc₁
  have hf₁qs : IsQuasiSeparated B S hS f₁.hom := isQuasiSeparated_of_isPullback B S hS sqι hfqs
  obtain ⟨e, ⟨he1, he2⟩, heuniq⟩ :=
    existsUnique_iso_normalizationInQcqs_of_isPullback_of_isFlat f hfqc hfqs huc sq hg sqP h hq hp
      hf₁qc hf₁qs
  refine ⟨huc₁, hf₁qc, hf₁qs, ?_, e, ⟨he1, he2⟩, heuniq⟩
  exact (isRelativeNormalization_normalizationInQcqs f₁ hf₁qc hf₁qs).of_iso
    ((ObjectProperty.ι _).mapIso e) (congrArg (fun m => m.hom) he1)
    (congrArg (fun m => m.hom) he2)

end Stein

end AlgebraicGeometry.Space

end
