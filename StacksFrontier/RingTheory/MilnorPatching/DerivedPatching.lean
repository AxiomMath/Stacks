module

public import StacksFrontier.RingTheory.MilnorPatching.FiniteProjectiveComplexes
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# The patched complex in the derived category of a fibre product of rings

Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective. Let `E` and `P`
be complexes of finite projective modules over `B` and over `A'`, let
`φ : E ⊗_B A ≅ P ⊗_{A'} A` be an isomorphism of complexes, and let `L` be the complex of finite
projective `B'`-modules patched from them (`MilnorPatching.patchedComplex`). This file carries out
the ring-level part of the proof of Stacks Tag 0DL7: the short exact sequence
`0 → L → E ⊕ P → P ⊗_{A'} A → 0`, the identification of its triangle with any distinguished
triangle on `E ⊕ P → P ⊗_{A'} A` in `D(B')`, and the computation of `L ⊗ᴸ_{B'} B` and
`L ⊗ᴸ_{B'} A'`.

## Main definitions

* `MilnorPatching.patchedShortComplex`: the sequence `0 → L → E ⊕ P → P ⊗_{A'} A → 0` of complexes
  of `B'`-modules. The first map is adjoint to `L ⊗_{B'} B ≅ E` and `L ⊗_{B'} A' ≅ P`, the second
  sends `(e, p)` to `φ (1 ⊗ e) - 1 ⊗ p`.
* `MilnorPatching.patchedComplexDerivedExtensionFstIso` and
  `MilnorPatching.patchedComplexDerivedExtensionSndIso`: `L ⊗ᴸ_{B'} B ≅ E` and `L ⊗ᴸ_{B'} A' ≅ P`
  for bounded above `E` and `P`.

## Main results

* `MilnorPatching.exists_patchedComplex_X_of_compatible` and `MilnorPatching.patchedComplex_X_ext`:
  each `L^n` is the fibre product of `E^n` and `P^n` over `P^n ⊗_{A'} A`.
* `MilnorPatching.patchedShortComplex_shortExact`: the sequence is short exact.
* `MilnorPatching.exists_iso_patchedComplex_of_distinguished`: a distinguished triangle
  `M' → E ⊕ P → P ⊗_{A'} A → M'[1]` in `D(B')` is identified with the triangle of the sequence,
  so that `M' ≅ L` compatibly with the maps to `E ⊕ P`.
* `MilnorPatching.derivedExtensionScalarsAdjunction_homEquiv_symm_Q_map`: the map
  `K ⊗ᴸ_R T ⟶ X` adjoint to the map `K ⟶ X|_R` adjoint to `ψ : K ⊗_R T ≅ X` is the comparison at
  `K` followed by `ψ`.
* `MilnorPatching.isIso_derivedExtensionScalars_fst_of_distinguished` and
  `MilnorPatching.isIso_derivedExtensionScalars_snd_of_distinguished`: for bounded above `E` and
  `P`, the maps `M' ⊗ᴸ_{B'} B ⟶ E` and `M' ⊗ᴸ_{B'} A' ⟶ P` adjoint to the components of
  `M' ⟶ E ⊕ P` are isomorphisms.

## Implementation notes

Derived categories are taken over arbitrary `HasDerivedCategory` instances, and derived extension
of scalars is any total left derived functor of degreewise extension of scalars, with the
adjunction `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` of Stacks
Tag 0GMT. The patched complex is K-flat, so the comparison with degreewise extension of scalars is
invertible on it.

That `L^n` is the fibre product is read off from the full faithfulness of extension of scalars on
finite projective `B'`-modules (Stacks Tag 0D2J), tested against `B'` itself.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleGlueing
open scoped ChangeOfRings

universe w w' w'' u

namespace MilnorPatching

section ExtendScalars

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- In an extension of scalars along `f`, `1 ⊗ (r • m) = f r ⊗ m`. -/
theorem one_tmul_smul_eq_tmul (f : R →+* S) (M : Type u) [AddCommGroup M] [Module R M] (r : R)
    (m : M) :
    letI : Module R S := Module.compHom S f
    (1 : S) ⊗ₜ[R] (r • m) = f r ⊗ₜ[R] m := by
  let : Module R S := Module.compHom S f
  rw [← TensorProduct.smul_tmul]
  change (f r * 1 : S) ⊗ₜ[R] m = f r ⊗ₜ[R] m
  rw [mul_one]

/-- A morphism out of the extension of scalars of `R` is determined by the image of `1 ⊗ 1`. -/
theorem extendScalars_self_hom_ext (f : R →+* S) {N : ModuleCat.{u} S}
    {α β : (ModuleCat.extendScalars.{u, u, u} f).obj (ModuleCat.of R R) ⟶ N}
    (h : α ((1 : S) ⊗ₜ[R,f] (1 : R)) = β ((1 : S) ⊗ₜ[R,f] (1 : R))) : α = β :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv _ _).injective
    (ModuleCat.hom_ext (LinearMap.ext_ring h))

/-- A morphism out of an iterated extension of scalars of `R` is determined by the image of
`1 ⊗ 1 ⊗ 1`. -/
theorem extendScalars_extendScalars_self_hom_ext (f : R →+* S) (g : S →+* T)
    {N : ModuleCat.{u} T}
    {α β : (ModuleCat.extendScalars.{u, u, u} g).obj
      ((ModuleCat.extendScalars.{u, u, u} f).obj (ModuleCat.of R R)) ⟶ N}
    (h : α ((1 : T) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] (1 : R))) =
      β ((1 : T) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] (1 : R)))) : α = β :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).homEquiv _ _).injective
    (extendScalars_self_hom_ext f h)

/-- A morphism out of an extension of scalars along `f` carries `1 ⊗ (r • m)` to
`f r • g (1 ⊗ m)`. -/
theorem extendScalars_hom_one_tmul_smul (f : R →+* S) {M : ModuleCat.{u} R}
    {N : ModuleCat.{u} S} (g : (ModuleCat.extendScalars.{u, u, u} f).obj M ⟶ N) (r : R) (m : M) :
    g ((1 : S) ⊗ₜ[R,f] (r • m)) = f r • g ((1 : S) ⊗ₜ[R,f] m) := by
  have h : ((1 : S) ⊗ₜ[R,f] (r • m) : (ModuleCat.extendScalars.{u, u, u} f).obj M) =
      ((f r * 1 : S) ⊗ₜ[R,f] m : (ModuleCat.extendScalars.{u, u, u} f).obj M) := by
    rw [mul_one]
    exact one_tmul_smul_eq_tmul f M r m
  exact (congrArg g h).trans (g.hom.map_smul (f r) ((1 : S) ⊗ₜ[R,f] m))

/-- The adjoint of a map `M ⟶ N|_R` sends `1 ⊗ m` to the image of `m`. -/
theorem extendRestrictScalarsAdj_homEquiv_symm_one_tmul (f : R →+* S) {M : ModuleCat.{u} R}
    {N : ModuleCat.{u} S} (g : M ⟶ (ModuleCat.restrictScalars.{u} f).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv M N).symm g
      ((1 : S) ⊗ₜ[R,f] m) = g m :=
  congrArg (fun k : M ⟶ (ModuleCat.restrictScalars.{u} f).obj N ↦ k m)
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv M N |>.apply_symm_apply g)

end ExtendScalars

section TestObject

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)

/-- The gluing isomorphism of the scalar extensions of a `B'`-module identifies the two images
of `1 ⊗ 1 ⊗ l`. -/
theorem fibreProductExtension_obj_iso_hom_one_tmul_one_tmul (M : ModuleCat.{u} s.fibreProduct)
    (l : M) :
    ((fibreProductExtension I s).obj M).iso.hom ((1 : A) ⊗ₜ[B,toBase]
        (@id ((ModuleCat.extendScalars.{u, u, u} s.pullbackCone.fst.hom).obj M)
          ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l))) =
      (1 : A) ⊗ₜ[A',surjection]
        (@id ((ModuleCat.extendScalars.{u, u, u} s.pullbackCone.snd.hom).obj M)
          ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l)) := by
  let eF := ModuleCat.extendScalarsComp.{u} s.pullbackCone.fst.hom toBase
  let eS := ModuleCat.extendScalarsComp.{u} s.pullbackCone.snd.hom surjection
  have hc := congrArg CommRingCat.Hom.hom s.pullbackCone.condition
  let z : (ModuleCat.extendScalars.{u, u, u} (toBase.comp s.pullbackCone.fst.hom)).obj M :=
    (1 : A) ⊗ₜ[s.fibreProduct,toBase.comp s.pullbackCone.fst.hom] l
  have hz := ModuleCat.extendScalarsComp_hom_app_one_tmul.{u} s.pullbackCone.fst.hom toBase M l
  have hi : eF.inv.app M (eF.hom.app M z) = z :=
    ConcreteCategory.congr_hom (eF.hom_inv_id_app M) z
  have h₂ : ∀ (g : s.pullbackCone.pt →+* A) (hg : toBase.comp s.pullbackCone.fst.hom = g),
      (eqToIso (congrArg ModuleCat.extendScalars hg)).hom.app M z =
        (1 : A) ⊗ₜ[s.fibreProduct,g] l := by
    rintro _ rfl
    rfl
  change eS.hom.app M ((eqToIso (congrArg ModuleCat.extendScalars hc)).hom.app M
    (eF.inv.app M ((1 : A) ⊗ₜ[B,toBase] ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l)))) = _
  refine (congrArg (fun t ↦ eS.hom.app M ((eqToIso (congrArg ModuleCat.extendScalars hc)).hom.app M
    t)) ((congrArg (eF.inv.app M) hz.symm).trans hi)).trans ?_
  refine (congrArg (eS.hom.app M) (h₂ _ hc)).trans ?_
  exact ModuleCat.extendScalarsComp_hom_app_one_tmul.{u} s.pullbackCone.snd.hom surjection M l

/-- A morphism of compatible pairs out of the scalar extensions of `B'` is determined by the
images of `1`. -/
theorem fibreProductExtension_self_hom_ext
    {X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection)}
    {m m' : (fibreProductExtension I s).obj (ModuleCat.of s.fibreProduct s.fibreProduct) ⟶ X}
    (h₁ : m.fst ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] (1 : s.fibreProduct)) =
      m'.fst ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] (1 : s.fibreProduct)))
    (h₂ : m.snd ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] (1 : s.fibreProduct)) =
      m'.snd ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] (1 : s.fibreProduct))) :
    m = m' :=
  CategoricalPullback.hom_ext (extendScalars_self_hom_ext _ h₁) (extendScalars_self_hom_ext _ h₂)

/-- A compatible pair of elements is the image of `1` under a morphism of compatible pairs out
of the scalar extensions of `B'`. -/
theorem exists_fibreProductExtension_self_hom
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection)) (e : X.fst) (p : X.snd)
    (h : X.iso.hom ((1 : A) ⊗ₜ[B,toBase] e) = (1 : A) ⊗ₜ[A',surjection] p) :
    ∃ m : (fibreProductExtension I s).obj (ModuleCat.of s.fibreProduct s.fibreProduct) ⟶ X,
      m.fst ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] (1 : s.fibreProduct)) = e ∧
        m.snd ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] (1 : s.fibreProduct)) = p := by
  let : Module s.fibreProduct X.fst := Module.compHom X.fst s.pullbackCone.fst.hom
  let : Module s.fibreProduct X.snd := Module.compHom X.snd s.pullbackCone.snd.hom
  let g₁ : ModuleCat.of s.fibreProduct s.fibreProduct ⟶
      (ModuleCat.restrictScalars.{u} s.pullbackCone.fst.hom).obj X.fst :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton s.fibreProduct X.fst e)
  let g₂ : ModuleCat.of s.fibreProduct s.fibreProduct ⟶
      (ModuleCat.restrictScalars.{u} s.pullbackCone.snd.hom).obj X.snd :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton s.fibreProduct X.snd p)
  let m₁ := ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} s.pullbackCone.fst.hom).homEquiv
    _ _).symm g₁
  let m₂ := ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} s.pullbackCone.snd.hom).homEquiv
    _ _).symm g₂
  have hm₁ : m₁ ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] (1 : s.fibreProduct)) = e :=
    (extendRestrictScalarsAdj_homEquiv_symm_one_tmul _ g₁ _).trans (one_smul _ e)
  have hm₂ : m₂ ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] (1 : s.fibreProduct)) =
      p :=
    (extendRestrictScalarsAdj_homEquiv_symm_one_tmul _ g₂ _).trans (one_smul _ p)
  refine ⟨{ fst := m₁, snd := m₂, w := ?_ }, hm₁, hm₂⟩
  apply extendScalars_extendScalars_self_hom_ext
  have hiso := fibreProductExtension_obj_iso_hom_one_tmul_one_tmul I s
    (ModuleCat.of s.fibreProduct s.fibreProduct) (1 : s.fibreProduct)
  change X.iso.hom ((1 : A) ⊗ₜ[B,toBase] (m₁ ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom]
      (1 : s.fibreProduct)))) =
    (ModuleCat.extendScalars.{u, u, u} surjection).map m₂
      (((fibreProductExtension I s).obj (ModuleCat.of s.fibreProduct s.fibreProduct)).iso.hom
        ((1 : A) ⊗ₜ[B,toBase] ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom]
          (1 : s.fibreProduct))))
  rw [hm₁, h]
  refine Eq.trans ?_ (congrArg ((ModuleCat.extendScalars.{u, u, u} surjection).map m₂) hiso.symm)
  change _ = (1 : A) ⊗ₜ[A',surjection] (m₂ ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom]
      (1 : s.fibreProduct)))
  rw [hm₂]

end TestObject

section PatchedModules

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)
  (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

/-- Extension of scalars is full on finite projective `B'`-modules, by Stacks Tag 0D2J. -/
instance : (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
    fibreProductExtension I s).Full :=
  Functor.Full.of_iso (finiteProjectivePatchingEquivalenceFunctorIso I s).symm

/-- `B'` as a finite projective module over itself. -/
abbrev fibreProductSelf : ObjectProperty.FullSubcategory (finiteProjectiveFibreProductModule I s) :=
  ⟨ModuleCat.of s.fibreProduct s.fibreProduct, ⟨inferInstance, inferInstance⟩⟩

/-- The degree `n` term of the patched complex, as a finite projective `B'`-module. -/
abbrev patchedComplexXFiniteProjective (n : ℤ) :
    ObjectProperty.FullSubcategory (finiteProjectiveFibreProductModule I s) :=
  ⟨(patchedComplex I s E P φ hE hP).X n, patchedComplex_finite_projective I s E P φ hE hP n⟩

/-- The morphism `B' ⟶ L^n` sending `1` to `l`. -/
def patchedComplexXSpan (n : ℤ) (l : (patchedComplex I s E P φ hE hP).X n) :
    fibreProductSelf I s ⟶ patchedComplexXFiniteProjective I s E P φ hE hP n :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton s.fibreProduct _ l))

/-- The two components of the identification of the scalar extensions of the patched module,
evaluated at `1 ⊗ l`. -/
theorem patchedComplexExtensionIso_fst_snd_one_tmul (n : ℤ)
    (l : (patchedComplex I s E P φ hE hP).X n) :
    ((fibreProductExtension I s).map (patchedComplexXSpan I s E P φ hE hP n l).hom ≫
        (patchedComplexExtensionIso I s E P φ hE hP n).hom).fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] (1 : s.fibreProduct)) =
      (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) ∧
    ((fibreProductExtension I s).map (patchedComplexXSpan I s E P φ hE hP n l).hom ≫
        (patchedComplexExtensionIso I s E P φ hE hP n).hom).snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] (1 : s.fibreProduct)) =
      (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l) := by
  constructor
  · change (patchedComplexExtensionIso I s E P φ hE hP n).hom.fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom]
          ((patchedComplexXSpan I s E P φ hE hP n l).hom (1 : s.fibreProduct))) =
      (patchedComplexExtensionIso I s E P φ hE hP n).hom.fst
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l)
    congr 2
    exact one_smul _ _
  · change (patchedComplexExtensionIso I s E P φ hE hP n).hom.snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom]
          ((patchedComplexXSpan I s E P φ hE hP n l).hom (1 : s.fibreProduct))) =
      (patchedComplexExtensionIso I s E P φ hE hP n).hom.snd
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l)
    congr 2
    exact one_smul _ _

/-- An element of the patched module is determined by its images in `E` and in `P`. -/
theorem patchedComplex_X_ext (n : ℤ) {l l' : (patchedComplex I s E P φ hE hP).X n}
    (h₁ : (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) =
      (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l'))
    (h₂ : (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l) =
      (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l')) :
    l = l' := by
  have hk : patchedComplexXSpan I s E P φ hE hP n l = patchedComplexXSpan I s E P φ hE hP n l' := by
    apply (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
      fibreProductExtension I s).map_injective
    change (fibreProductExtension I s).map (patchedComplexXSpan I s E P φ hE hP n l).hom =
      (fibreProductExtension I s).map (patchedComplexXSpan I s E P φ hE hP n l').hom
    refine (cancel_mono (patchedComplexExtensionIso I s E P φ hE hP n).hom).1 ?_
    have e := patchedComplexExtensionIso_fst_snd_one_tmul I s E P φ hE hP n l
    have e' := patchedComplexExtensionIso_fst_snd_one_tmul I s E P φ hE hP n l'
    exact fibreProductExtension_self_hom_ext I s (e.1.trans (h₁.trans e'.1.symm))
      (e.2.trans (h₂.trans e'.2.symm))
  have := congrArg (fun k ↦ k.hom (1 : s.fibreProduct)) hk
  change (1 : s.fibreProduct) • l = (1 : s.fibreProduct) • l' at this
  simpa using this

/-- **The patched module is the fibre product of `E^n` and `P^n` over `P^n ⊗_{A'} A`.** Every
pair of elements of `E^n` and `P^n` with the same image under `φ` comes from an element of the
patched module. -/
theorem exists_patchedComplex_X_of_compatible (n : ℤ) (e : E.X n) (p : P.X n)
    (h : φ.hom.f n ((1 : A) ⊗ₜ[B,toBase] e) = (1 : A) ⊗ₜ[A',surjection] p) :
    ∃ l : (patchedComplex I s E P φ hE hP).X n,
      (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n
          ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) = e ∧
        (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n
          ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l) = p := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_fibreProductExtension_self_hom I s (complexPatchObj E P φ n) e p h
  obtain ⟨k, hk⟩ := (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
    fibreProductExtension I s).map_surjective (X := fibreProductSelf I s)
    (Y := patchedComplexXFiniteProjective I s E P φ hE hP n)
    (m ≫ (patchedComplexExtensionIso I s E P φ hE hP n).inv)
  have hk' : patchedComplexXSpan I s E P φ hE hP n (k.hom (1 : s.fibreProduct)) = k := by
    ext : 1
    exact ModuleCat.hom_ext (LinearMap.ext_ring (one_smul _ _))
  have hm : (fibreProductExtension I s).map
      (patchedComplexXSpan I s E P φ hE hP n (k.hom (1 : s.fibreProduct))).hom ≫
        (patchedComplexExtensionIso I s E P φ hE hP n).hom = m := by
    rw [hk']
    exact (Iso.eq_comp_inv _).1 hk
  have e := patchedComplexExtensionIso_fst_snd_one_tmul I s E P φ hE hP n
    (k.hom (1 : s.fibreProduct))
  rw [hm] at e
  exact ⟨k.hom (1 : s.fibreProduct), e.1.symm.trans hm₁, e.2.symm.trans hm₂⟩

end PatchedModules

section ShortExact

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)
  (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

/-- The projection `B' → B`. -/
abbrev fibreProductFst : s.fibreProduct →+* B := s.pullbackCone.fst.hom

/-- The projection `B' → A'`. -/
abbrev fibreProductSnd : s.fibreProduct →+* A' := s.pullbackCone.snd.hom

/-- The map `B' → A` through `A'`. -/
abbrev fibreProductToBase : s.fibreProduct →+* A := surjection.comp (fibreProductSnd I s)

/-- `E`, read as a complex of `B'`-modules. -/
abbrev restrictedFst : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ :=
  ((ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E

/-- `P`, read as a complex of `B'`-modules. -/
abbrev restrictedSnd : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ :=
  ((ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- `P ⊗_{A'} A`, read as a complex of `B'`-modules. -/
abbrev restrictedBase : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ :=
  ((ModuleCat.restrictScalars.{u} (fibreProductToBase I s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)

/-- The two maps `B' → A` agree. -/
theorem fibreProduct_toBase_fst (r : s.fibreProduct) :
    toBase (fibreProductFst I s r) = fibreProductToBase I s r :=
  RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.pullbackCone.condition) r

/-- The map of complexes `E ⟶ P ⊗_{A'} A` of `B'`-modules, `e ↦ φ (1 ⊗ e)`. -/
def compatibleFstMap : restrictedFst I s E ⟶ restrictedBase I s P where
  f n := (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} toBase).unit.app (E.X n) ≫
        (ModuleCat.restrictScalars.{u} toBase).map (φ.hom.f n)) ≫
    (ModuleCat.restrictScalarsComp'App.{u} (fibreProductFst I s) toBase (fibreProductToBase I s)
      (RingHom.ext (fun r ↦ (fibreProduct_toBase_fst I s r).symm)) _).inv
  comm' i j _ := by
    ext x
    exact ConcreteCategory.congr_hom (φ.hom.comm i j) ((1 : A) ⊗ₜ[B,toBase] (@id (E.X i) x))

/-- The map of complexes `P ⟶ P ⊗_{A'} A` of `B'`-modules, `p ↦ 1 ⊗ p`. -/
def compatibleSndMap : restrictedSnd I s P ⟶ restrictedBase I s P where
  f n := (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} surjection).unit.app (P.X n)) ≫
    (ModuleCat.restrictScalarsComp'App.{u} (fibreProductSnd I s) surjection
      (fibreProductToBase I s) rfl _).inv
  comm' i j _ := by
    ext x
    rfl

/-- `compatibleFstMap` sends `e` to `φ (1 ⊗ e)`. -/
theorem compatibleFstMap_f_apply (n : ℤ) (e : E.X n) :
    (compatibleFstMap I s E P φ).f n e = φ.hom.f n ((1 : A) ⊗ₜ[B,toBase] e) :=
  rfl

/-- `compatibleSndMap` sends `p` to `1 ⊗ p`. -/
theorem compatibleSndMap_f_apply (n : ℤ) (p : P.X n) :
    (compatibleSndMap I s P).f n p = (1 : A) ⊗ₜ[A',surjection] p :=
  rfl

/-- The map of complexes `L ⟶ E` of `B'`-modules adjoint to `L ⊗_{B'} B ≅ E`. -/
def patchedComplexToFst : patchedComplex I s E P φ hE hP ⟶ restrictedFst I s E :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (fibreProductFst I s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _ (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom

/-- The map of complexes `L ⟶ P` of `B'`-modules adjoint to `L ⊗_{B'} A' ≅ P`. -/
def patchedComplexToSnd : patchedComplex I s E P φ hE hP ⟶ restrictedSnd I s P :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (fibreProductSnd I s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _ (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom

/-- `patchedComplexToFst` sends `l` to the image of `1 ⊗ l` in `E`. -/
theorem patchedComplexToFst_f_apply (n : ℤ) (l : (patchedComplex I s E P φ hE hP).X n) :
    (patchedComplexToFst I s E P φ hE hP).f n l =
      (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l) :=
  rfl

/-- `patchedComplexToSnd` sends `l` to the image of `1 ⊗ l` in `P`. -/
theorem patchedComplexToSnd_f_apply (n : ℤ) (l : (patchedComplex I s E P φ hE hP).X n) :
    (patchedComplexToSnd I s E P φ hE hP).f n l =
      (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n
        ((1 : A') ⊗ₜ[s.fibreProduct,s.pullbackCone.snd.hom] l) :=
  rfl

/-- The two composites `L ⟶ P ⊗_{A'} A` agree: this is the compatibility of the identifications
`L ⊗_{B'} B ≅ E` and `L ⊗_{B'} A' ≅ P` with `φ`. -/
theorem patchedComplexToFst_comp_compatibleFstMap :
    patchedComplexToFst I s E P φ hE hP ≫ compatibleFstMap I s E P φ =
      patchedComplexToSnd I s E P φ hE hP ≫ compatibleSndMap I s P := by
  ext n l
  have h := ConcreteCategory.congr_hom
    (patchedComplexExtendScalarsIso_compatible I s E P φ hE hP n)
    ((1 : A) ⊗ₜ[B,toBase] (@id ((ModuleCat.extendScalars.{u, u, u} s.pullbackCone.fst.hom).obj
      ((patchedComplex I s E P φ hE hP).X n))
        ((1 : B) ⊗ₜ[s.fibreProduct,s.pullbackCone.fst.hom] l)))
  exact h.trans (congrArg ((ModuleCat.extendScalars.{u, u, u} surjection).map
    ((patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n))
    (fibreProductExtension_obj_iso_hom_one_tmul_one_tmul I s
      ((patchedComplex I s E P φ hE hP).X n) l))

/-- **The short exact sequence `0 → L → E ⊕ P → P ⊗_{A'} A → 0`** of complexes of `B'`-modules:
the first map has components the maps adjoint to `L ⊗_{B'} B ≅ E` and `L ⊗_{B'} A' ≅ P`, and
the second sends `(e, p)` to `φ (1 ⊗ e) - 1 ⊗ p`. -/
def patchedShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ) :=
  ShortComplex.mk
    (biprod.lift (patchedComplexToFst I s E P φ hE hP) (patchedComplexToSnd I s E P φ hE hP))
    (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P)) (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
      exact patchedComplexToFst_comp_compatibleFstMap I s E P φ hE hP)

/-- The sequence `0 → L → E ⊕ P → P ⊗_{A'} A → 0` is short exact. -/
theorem patchedShortComplex_shortExact :
    (patchedShortComplex I s E P φ hE hP).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  let u₁ := patchedComplexToFst I s E P φ hE hP
  let u₂ := patchedComplexToSnd I s E P φ hE hP
  let v₁ := compatibleFstMap I s E P φ
  let v₂ := compatibleSndMap I s P
  let X₂ := restrictedFst I s E ⊞ restrictedSnd I s P
  have hfst : ∀ l, (biprod.fst : X₂ ⟶ _).f n ((biprod.lift u₁ u₂).f n l) = u₁.f n l := fun l ↦ by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, biprod.lift_fst]
  have hsnd : ∀ l, (biprod.snd : X₂ ⟶ _).f n ((biprod.lift u₁ u₂).f n l) = u₂.f n l := fun l ↦ by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, biprod.lift_snd]
  have hdecomp : ∀ y : X₂.X n, (biprod.inl : _ ⟶ X₂).f n ((biprod.fst : X₂ ⟶ _).f n y) +
      (biprod.inr : _ ⟶ X₂).f n ((biprod.snd : X₂ ⟶ _).f n y) = y := fun y ↦
    ConcreteCategory.congr_hom
      (congrArg (fun t : X₂ ⟶ X₂ ↦ t.f n) (biprod.total (X := restrictedFst I s E)
        (Y := restrictedSnd I s P))) y
  have hext : ∀ y y' : X₂.X n, (biprod.fst : X₂ ⟶ _).f n y = (biprod.fst : X₂ ⟶ _).f n y' →
      (biprod.snd : X₂ ⟶ _).f n y = (biprod.snd : X₂ ⟶ _).f n y' → y = y' :=
    fun y y' h₁ h₂ ↦ by rw [← hdecomp y, ← hdecomp y', h₁, h₂]
  have hl : ∀ e, (biprod.desc v₁ (-v₂)).f n ((biprod.inl : _ ⟶ X₂).f n e) = v₁.f n e :=
    fun e ↦ ConcreteCategory.congr_hom (congrArg (fun t ↦ t.f n) (biprod.inl_desc v₁ (-v₂))) e
  have hr : ∀ p, (biprod.desc v₁ (-v₂)).f n ((biprod.inr : _ ⟶ X₂).f n p) = -v₂.f n p :=
    fun p ↦ ConcreteCategory.congr_hom (congrArg (fun t ↦ t.f n) (biprod.inr_desc v₁ (-v₂))) p
  have hg : ∀ y : X₂.X n, (biprod.desc v₁ (-v₂)).f n y =
      v₁.f n ((biprod.fst : X₂ ⟶ _).f n y) - v₂.f n ((biprod.snd : X₂ ⟶ _).f n y) := by
    intro y
    conv_lhs => rw [← hdecomp y]
    rw [map_add, hl, hr, sub_eq_add_neg]
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    change ↑(X₂.X n) at y
    change (biprod.desc v₁ (-v₂)).f n y = 0 at hy
    rw [hg, sub_eq_zero] at hy
    obtain ⟨l, h₁, h₂⟩ := exists_patchedComplex_X_of_compatible I s E P φ hE hP n _ _ hy
    exact ⟨l, hext _ _ ((hfst l).trans h₁) ((hsnd l).trans h₂)⟩
  · rw [ModuleCat.mono_iff_injective]
    intro l l' h
    change ↑((patchedComplex I s E P φ hE hP).X n) at l l'
    change (biprod.lift u₁ u₂).f n l = (biprod.lift u₁ u₂).f n l' at h
    exact patchedComplex_X_ext I s E P φ hE hP n
      ((hfst l).symm.trans ((congrArg ((biprod.fst : X₂ ⟶ _).f n) h).trans (hfst l')))
      ((hsnd l).symm.trans ((congrArg ((biprod.snd : X₂ ⟶ _).f n) h).trans (hsnd l')))
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨p, hp⟩ := tensorUnit_surjective surjection s.surjective_surjection (P.X n) y
    let p' : (restrictedSnd I s P).X n := p
    refine ⟨(biprod.inr : _ ⟶ X₂).f n (-p'), (hr (-p')).trans ?_⟩
    rwa [map_neg, neg_neg]

end ShortExact

section DerivedExtension

variable {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} T)]
  (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
  (α : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- Let `ψ : K ⊗_R T ≅ X` be an isomorphism of complexes. The map `K ⊗ᴸ_R T ⟶ X` adjoint to the
map `K ⟶ X|_R` adjoint to `ψ` is the comparison of `F` with degreewise extension of scalars at `K`
followed by `ψ`. -/
theorem derivedExtensionScalarsAdjunction_homEquiv_symm_Q_map
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : CochainComplex (ModuleCat.{u} T) ℤ)
    (ψ : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ X) :
    ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      f F α).homEquiv _ _).symm
        (DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).homEquiv _ _ ψ.hom) ≫
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app X) =
      α.app K ≫ DerivedCategory.Q.map ψ.hom := by
  let : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive
  rw [Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app.{u, u, u}
      f F α X, ← Category.assoc, ← Functor.comp_map, α.naturality, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  have hc : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv K X ψ.hom) ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).counit.app X = ψ.hom :=
    (Adjunction.homEquiv_counit _ _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  rw [hc]

/-- Let `K` be a K-flat complex over `R` and `ψ : K ⊗_R T ≅ X` an isomorphism of complexes. The
map `K ⊗ᴸ_R T ⟶ X` adjoint to the map `K ⟶ X|_R` adjoint to `ψ` is an isomorphism. -/
theorem isIso_derivedExtensionScalarsAdjunction_homEquiv_symm
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (X : CochainComplex (ModuleCat.{u} T) ℤ)
    (ψ : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ X) :
    IsIso (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      f F α).homEquiv _ _).symm
        (DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).homEquiv _ _ ψ.hom) ≫
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app X)) := by
  let : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive
  have hα : IsIso (α.app K) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u} f F α K hK
  rw [derivedExtensionScalarsAdjunction_homEquiv_symm_Q_map]
  infer_instance

/-- For K-flat `K`, a map `M' ⟶ X|_R` that is `M' ≅ K` followed by the adjoint of `ψ` is adjoint to
an isomorphism. -/
private theorem isIso_homEquiv_symm_of_eq_comp
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (X : CochainComplex (ModuleCat.{u} T) ℤ)
    (ψ : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ X) {M' : DerivedCategory (ModuleCat.{u} R)}
    (e₁ : M' ≅ DerivedCategory.Q.obj K)
    (m : M' ⟶ DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X))
    (h : m = e₁.hom ≫ DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv _ _ ψ.hom)) :
    IsIso (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      f F α).homEquiv _ _).symm
        (m ≫ (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app X)) := by
  rw [h, Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  exact IsIso.comp_isIso' inferInstance
    (isIso_derivedExtensionScalarsAdjunction_homEquiv_symm f F α K hK X ψ)

end DerivedExtension

section Derived

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)
  (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

open Pretriangulated

/-- The patched complex is bounded above when `E` and `P` are. -/
theorem patchedComplex_isStrictlyLE (d : ℤ) [E.IsStrictlyLE d] [P.IsStrictlyLE d] :
    (patchedComplex I s E P φ hE hP).IsStrictlyLE d :=
  (CochainComplex.isStrictlyLE_iff _ d).2 fun i hi ↦
    isZero_patchedComplex_X I s E P φ hE hP i (E.isZero_of_isStrictlyLE d i hi)
      (P.isZero_of_isStrictlyLE d i hi)

/-- The patched complex is K-flat when `E` and `P` are bounded above. -/
theorem patchedComplex_kFlat (d : ℤ) [E.IsStrictlyLE d] [P.IsStrictlyLE d] :
    CochainComplex.KFlat.{u, u} (patchedComplex I s E P φ hE hP) := by
  have := patchedComplex_isStrictlyLE I s E P φ hE hP d
  have : ∀ n, Module.Flat s.fibreProduct ((patchedComplex I s E P φ hE hP).X n) := fun n ↦ by
    have := (patchedComplex_finite_projective I s E P φ hE hP n).2
    exact Module.Flat.of_projective
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} _ d

variable [HasDerivedCategory.{w} (ModuleCat.{u} s.fibreProduct)]

/-- The distinguished triangle `L → E ⊕ P → P ⊗_{A'} A → L[1]` in `D(B')` given by the short
exact sequence `patchedShortComplex`. -/
abbrev patchedTriangle : Triangle (DerivedCategory (ModuleCat.{u} s.fibreProduct)) :=
  DerivedCategory.triangleOfSES (patchedShortComplex_shortExact I s E P φ hE hP)

/-- The triangle of the short exact sequence `0 → L → E ⊕ P → P ⊗_{A'} A → 0` is
distinguished. -/
theorem patchedTriangle_distinguished :
    patchedTriangle I s E P φ hE hP ∈ distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct)) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- **A distinguished triangle on `E ⊕ P ⟶ P ⊗_{A'} A` has first vertex `L`.** Given a
distinguished triangle `M' → E ⊕ P → P ⊗_{A'} A → M'[1]` in `D(B')` whose second morphism is the
map `(e, p) ↦ φ (1 ⊗ e) - 1 ⊗ p`, there is an isomorphism `M' ≅ L` under which the first
morphism is `L ⟶ E ⊕ P`. -/
theorem exists_iso_patchedComplex_of_distinguished
    (Tr : Triangle (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (hTr : Tr ∈ distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (e₂ : Tr.obj₂ ≅ DerivedCategory.Q.obj (restrictedFst I s E ⊞ restrictedSnd I s P))
    (e₃ : Tr.obj₃ ≅ DerivedCategory.Q.obj (restrictedBase I s P))
    (comm : Tr.mor₂ ≫ e₃.hom =
      e₂.hom ≫ DerivedCategory.Q.map
        (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P))) :
    ∃ e₁ : Tr.obj₁ ≅ DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP),
      Tr.mor₁ ≫ e₂.hom = e₁.hom ≫ DerivedCategory.Q.map
        (biprod.lift (patchedComplexToFst I s E P φ hE hP)
          (patchedComplexToSnd I s E P φ hE hP)) := by
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ Tr
    (patchedTriangle I s E P φ hE hP) hTr (patchedTriangle_distinguished I s E P φ hE hP)
    e₂.hom e₃.hom comm
  have : IsIso a := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a e₂.hom e₃.hom ha₁ comm ha₃) hTr
    (patchedTriangle_distinguished I s E P φ hE hP) (inferInstanceAs (IsIso e₂.hom))
    (inferInstanceAs (IsIso e₃.hom))
  exact ⟨@asIso _ _ _ _ a this, ha₁⟩

section DerivedTensor

variable [HasDerivedCategory.{w'} (ModuleCat.{u} B)] [HasDerivedCategory.{w''} (ModuleCat.{u} A')]
  (F₁ : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} B))
  (α₁ : DerivedCategory.Q ⋙ F₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} (fibreProductFst I s)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F₁.IsLeftDerivedFunctor α₁
    (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ))]
  (F₂ : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} A'))
  (α₂ : DerivedCategory.Q ⋙ F₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} (fibreProductSnd I s)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F₂.IsLeftDerivedFunctor α₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ))]

/-- **`L ⊗ᴸ_{B'} B ≅ E`**: the patched complex is K-flat, so its derived extension of scalars to
`B` is computed degreewise. -/
def patchedComplexDerivedExtensionFstIso (d : ℤ) [E.IsStrictlyLE d] [P.IsStrictlyLE d] :
    F₁.obj (DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP)) ≅ DerivedCategory.Q.obj E :=
  letI : (ModuleCat.extendScalars.{u, u, u} (fibreProductFst I s)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (fibreProductFst I s)).left_adjoint_additive
  haveI := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u}
    (fibreProductFst I s) F₁ α₁ _ (patchedComplex_kFlat I s E P φ hE hP d)
  asIso (α₁.app (patchedComplex I s E P φ hE hP)) ≪≫
    DerivedCategory.Q.mapIso (patchedComplexExtendScalarsFstIso I s E P φ hE hP)

/-- **`L ⊗ᴸ_{B'} A' ≅ P`**: the patched complex is K-flat, so its derived extension of scalars
to `A'` is computed degreewise. -/
def patchedComplexDerivedExtensionSndIso (d : ℤ) [E.IsStrictlyLE d] [P.IsStrictlyLE d] :
    F₂.obj (DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP)) ≅ DerivedCategory.Q.obj P :=
  letI : (ModuleCat.extendScalars.{u, u, u} (fibreProductSnd I s)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (fibreProductSnd I s)).left_adjoint_additive
  haveI := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u}
    (fibreProductSnd I s) F₂ α₂ _ (patchedComplex_kFlat I s E P φ hE hP d)
  asIso (α₂.app (patchedComplex I s E P φ hE hP)) ≪≫
    DerivedCategory.Q.mapIso (patchedComplexExtendScalarsSndIso I s E P φ hE hP)

variable (Tr : Triangle (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
  (hTr : Tr ∈ distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
  (e₂ : Tr.obj₂ ≅ DerivedCategory.Q.obj (restrictedFst I s E ⊞ restrictedSnd I s P))
  (e₃ : Tr.obj₃ ≅ DerivedCategory.Q.obj (restrictedBase I s P))
  (comm : Tr.mor₂ ≫ e₃.hom =
    e₂.hom ≫ DerivedCategory.Q.map
      (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P)))

omit [HasDerivedCategory.{w''} (ModuleCat.{u} A')] in
include hE hP hTr comm in
/-- **The ring-level statement in the proof of Stacks 0DL7, first half.** Let
`M' → E ⊕ P → P ⊗_{A'} A → M'[1]` be a distinguished triangle in `D(B')` whose second morphism
is `(e, p) ↦ φ (1 ⊗ e) - 1 ⊗ p`, with `E` and `P` bounded above. The map `M' ⊗ᴸ_{B'} B ⟶ E`
adjoint to the first component of `M' ⟶ E ⊕ P` is an isomorphism. -/
theorem isIso_derivedExtensionScalars_fst_of_distinguished (d : ℤ) [E.IsStrictlyLE d]
    [P.IsStrictlyLE d] :
    IsIso (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      (fibreProductFst I s) F₁ α₁).homEquiv _ _).symm
        (Tr.mor₁ ≫ e₂.hom ≫ DerivedCategory.Q.map biprod.fst ≫
          (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategoryFactors.inv.app
            E)) := by
  obtain ⟨e₁, h₁⟩ := exists_iso_patchedComplex_of_distinguished I s E P φ hE hP Tr hTr e₂ e₃ comm
  have h : Tr.mor₁ ≫ e₂.hom ≫ DerivedCategory.Q.map biprod.fst =
      e₁.hom ≫ DerivedCategory.Q.map (patchedComplexToFst I s E P φ hE hP) := by
    rw [← Category.assoc Tr.mor₁, h₁, Category.assoc, ← Functor.map_comp, biprod.lift_fst]
  simpa only [Category.assoc] using isIso_homEquiv_symm_of_eq_comp (fibreProductFst I s) F₁ α₁ _
    (patchedComplex_kFlat I s E P φ hE hP d) E
    (patchedComplexExtendScalarsFstIso I s E P φ hE hP) e₁ _ h

omit [HasDerivedCategory.{w'} (ModuleCat.{u} B)] in
include hE hP hTr comm in
/-- **The ring-level statement in the proof of Stacks 0DL7, second half.** In the situation of
`isIso_derivedExtensionScalars_fst_of_distinguished`, the map `M' ⊗ᴸ_{B'} A' ⟶ P` adjoint to the
second component of `M' ⟶ E ⊕ P` is an isomorphism. -/
theorem isIso_derivedExtensionScalars_snd_of_distinguished (d : ℤ) [E.IsStrictlyLE d]
    [P.IsStrictlyLE d] :
    IsIso (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      (fibreProductSnd I s) F₂ α₂).homEquiv _ _).symm
        (Tr.mor₁ ≫ e₂.hom ≫ DerivedCategory.Q.map biprod.snd ≫
          (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategoryFactors.inv.app
            P)) := by
  obtain ⟨e₁, h₁⟩ := exists_iso_patchedComplex_of_distinguished I s E P φ hE hP Tr hTr e₂ e₃ comm
  have h : Tr.mor₁ ≫ e₂.hom ≫ DerivedCategory.Q.map biprod.snd =
      e₁.hom ≫ DerivedCategory.Q.map (patchedComplexToSnd I s E P φ hE hP) := by
    rw [← Category.assoc Tr.mor₁, h₁, Category.assoc, ← Functor.map_comp, biprod.lift_snd]
  simpa only [Category.assoc] using isIso_homEquiv_symm_of_eq_comp (fibreProductSnd I s) F₂ α₂ _
    (patchedComplex_kFlat I s E P φ hE hP d) P
    (patchedComplexExtendScalarsSndIso I s E P φ hE hP) e₁ _ h

end DerivedTensor

end Derived

end MilnorPatching
