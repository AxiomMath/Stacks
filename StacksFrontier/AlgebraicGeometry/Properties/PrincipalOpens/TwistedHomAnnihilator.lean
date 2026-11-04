module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingGradedHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionsCore

/-!
# A local annihilator for a twisted section of the internal Hom sheaf

Let `X` be a scheme, let `L` be an invertible `𝒪_X`-module with global section `s`, and let `ℱ`
and `𝒢` be quasi-coherent `𝒪_X`-modules with `ℱ` of finite type. A global section `t` of
`ℋom(ℱ, 𝒢) ⊗ L^{⊗ n}` vanishing on the open `X_s` where `s` does not vanish is annihilated, near
every point of `X`, by a power of a local equation for `s`: there is an open `U` around the point
on which `s|_U = r · l` and `r ^ e · t|_U = 0`.

This is the local half of the injectivity statement of
[Stacks, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ) part (1) for the comparison map of
[Stacks, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M); it is exactly the hypothesis
`Stacks.SheafOfModules.homLocalizationMap_injective_of_locally` consumes, and the quasi-compact
gluing that turns it into one global exponent is
`Stacks.SheafOfModules.exists_pow_smul_eq_zero_of_locally`.

## Main results

* `Stacks.SheafOfModules.exists_pow_smul_internalHomTwist_restrict_eq_zero`: the local
  annihilator at a point of `X`.

## Implementation notes

The argument of the source is carried out on an affine open `W` chosen inside three
neighbourhoods of the given point: one on which `L` has a frame, one on which `L^{⊗ n}` is
isomorphic to `𝒪_X`, and the neighbourhood carrying finitely many generators of `ℱ`. The frame
of `L` turns `s|_W` into `r · l` and identifies `X_s ∩ W` with `X.basicOpen r`; the
trivialization of `L^{⊗ n}` turns `t|_W` into a morphism `ℱ|_W ⟶ 𝒢|_W` vanishing on
`X.basicOpen r`; and over an affine open a section of a quasi-coherent module vanishing on a
basic open is killed by a power of its equation, applied to the finitely many generators of `ℱ`
and then to all sections by local generation.

## References

* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped _root_.TensorProduct

universe u

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf

/- A sheaf of modules produced by `Stacks.SheafOfModules.Tensor.sheafTensor` is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is the structure sheaf of this scheme again --
the same sheaf of rings as `structureSheafRing X.toRingedSpace` by `rfl`. It is a plain `def`,
so instance search cannot cross it, and the module structure on a section of a twist is then
not found. Make it transparent here, so that the scalar action on a twisted section is the one
the file's other statements use. -/
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

section TwistedAnnihilator

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] moduleOfSections
  Stacks.SheafOfModules.tensorRightEquiv

/-- **Restriction of a vanishing section.** If a section vanishes along `f`, it vanishes along
any `h` that factors `f` through some `g`, in a category where parallel arrows agree. -/
private lemma map_eq_zero_of_map_comp_eq_zero {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (T : PresheafOfModules R) {A B D : Cᵒᵖ} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ D) [Subsingleton (A ⟶ D)] {t : T.obj A} (hf : T.map f t = 0) : T.map h t = 0 := by
  rw [Subsingleton.elim h (f ≫ g), PresheafOfModules.map_comp_apply, hf, map_zero]

/-- **A uniform annihilator for a morphism vanishing on a basic open.** If a morphism
`φ : ℱ|_U ⟶ 𝒢|_U` of quasi-coherent modules over an affine open `U` carrying finitely many
generators of `ℱ` vanishes on every open inside `X.basicOpen r`, then one power of `r`
annihilates every component of `φ`. -/
private lemma exists_pow_smul_overHom_eq_zero
    {Y : Scheme.{u}} {F G : Y.Modules} [G.IsQuasicoherent]
    {y : Y} (q : LocalGenerators F y)
    {U : Y.Opens} (hU : IsAffineOpen U) (hUq : U ≤ q.nhd)
    (r : Γ(Y, U)) (φ : F.over U ⟶ G.over U)
    (hφ : ∀ (V : Y.Opens) (hVU : V ≤ U) (_ : V ≤ Y.basicOpen r) (b : Γ(F, V)),
      (SheafHomStalk.appAtR hVU φ b : Γ(G, V)) = 0) :
    ∃ N : ℕ, ∀ (V : Y.Opens) (hVU : V ≤ U) (b : Γ(F, V)),
      (Y.presheaf.map (homOfLE hVU).op (r ^ N)) •
        (SheafHomStalk.appAtR hVU φ b : Γ(G, V)) = 0 := by
  classical
  have : Fintype q.Gen := q.fintypeGen
  let a (i : q.Gen) : Γ(F, U) := F.val.map (homOfLE hUq).op (q.gens i)
  have hgen (i : q.Gen) :
      ∃ N : ℕ, r ^ N • (SheafHomStalk.appAtR le_rfl φ (a i) : Γ(G, U)) = 0 := by
    apply Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero G hU r
    have hnat := PresheafOfModules.naturality_apply φ.val
      (op (Over.homMk (homOfLE (Y.basicOpen_le r)) :
        Over.mk (homOfLE (Y.basicOpen_le r)) ⟶ Over.mk (𝟙 U))) (a i)
    exact hnat.symm.trans (hφ _ (Y.basicOpen_le r) le_rfl _)
  choose N hN using hgen
  let M := Finset.univ.sup N
  let ψ : F.over U ⟶ G.over U := ⟨_root_.smulHom Y.presheaf F.val G.val U (r ^ M) φ.val⟩
  have hψ (i : q.Gen) : (SheafHomStalk.appAtR le_rfl ψ (a i) : Γ(G, U)) = 0 := by
    change (Y.presheaf.map (𝟙 U).op (r ^ M)) •
      (SheafHomStalk.appAtR le_rfl φ (a i) : Γ(G, U)) = 0
    have hr : Y.presheaf.map (𝟙 U).op (r ^ M) = r ^ M :=
      ConcreteCategory.congr_hom (Y.presheaf.map_id (op U)) (r ^ M)
    rw [hr]
    have hle : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hN i, smul_zero]
  refine ⟨M, ?_⟩
  intro V hVU b
  have h := SheafHomStalk.appAtR_eq_zero_of_gens (Rc := Y.toRingedSpace.sheaf) q hUq ψ le_rfl
    (fun i => by
      change G.val.presheaf.map (𝟙 (op U)) (SheafHomStalk.appAtR le_rfl ψ (a i)) = 0
      rw [G.val.presheaf.map_id]
      exact hψ i) hVU b
  change (Y.presheaf.map (homOfLE hVU).op (r ^ M)) •
    (SheafHomStalk.appAtR hVU φ b : Γ(G, V)) = 0 at h
  exact h

/-- **A uniform annihilator for a section of the internal Hom sheaf.** A section of
`ℋom(ℱ, 𝒢)` over an affine open `U` carrying finitely many generators of `ℱ` which restricts to
zero on every open inside `X.basicOpen r` is annihilated by one power of `r`.

This is `Stacks.SheafOfModules.exists_pow_smul_overHom_eq_zero` read on the sections of the
internal Hom sheaf rather than on the morphism `ℱ|_U ⟶ 𝒢|_U` that such a section names.
Identifying the two readings is the costliest unification of the twisted statement below, and
heartbeats are counted cumulatively over a declaration, so it is carried out here, where the
section is a variable and no tensor product occurs. -/
private lemma exists_pow_smul_homSection_eq_zero
    {Y : Scheme.{u}} {F G : Y.Modules} [G.IsQuasicoherent]
    {y : Y} (q : LocalGenerators F y)
    {U : Y.Opens} (hU : IsAffineOpen U) (hUq : U ≤ q.nhd) (r : Γ(Y, U))
    (a : (sheafHomSpace Y.toRingedSpace F G).val.obj (op U))
    (ha : ∀ (W : Y.Opens) (hWU : W ≤ U) (_ : W ≤ Y.basicOpen r),
      (sheafHomSpace Y.toRingedSpace F G).val.map (homOfLE hWU).op a = 0) :
    ∃ N : ℕ, r ^ N • a = 0 := by
  let φ : F.over U ⟶ G.over U := ⟨a⟩
  obtain ⟨N, hN⟩ := exists_pow_smul_overHom_eq_zero q hU hUq r φ (by
    intro W hWU hWr b
    exact congrArg (fun z => (z.app (op (Over.mk (𝟙 W)))) b) (ha W hWU hWr))
  refine ⟨N, PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun b => ?_)⟩
  exact hN W.unop.left W.unop.hom.le b

/-- **A uniform annihilator for a twisted section of the internal Hom sheaf, locally.** Over an
affine open `U` carrying finitely many generators of `ℱ` and contained in an open trivializing
`P`, a section of `ℋom(ℱ, 𝒢) ⊗ P` restricting to zero on `X.basicOpen r` is annihilated by one
power of `r`. -/
private lemma exists_pow_smul_tensorHomSection_eq_zero
    {Y : Scheme.{u}} {F G P : Y.Modules} [G.IsQuasicoherent]
    {y : Y} (q : LocalGenerators F y)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hUq : U ≤ q.nhd) (hUV : U ≤ V)
    (e : P.over V ≅ _root_.SheafOfModules.unit
      ((structureSheafRing Y.toRingedSpace).over V)) (r : Γ(Y, U))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨sectionSiteRing Y, Y.toRingedSpace.IsSheaf⟩).obj ((sheafHomSpace Y.toRingedSpace F G))).obj (P))).val.obj (op U))
    (ht : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨sectionSiteRing Y, Y.toRingedSpace.IsSheaf⟩).obj ((sheafHomSpace Y.toRingedSpace F G))).obj (P))).val.map
        (homOfLE (Y.basicOpen_le r)).op t = 0) :
    ∃ N : ℕ, r ^ N • t = 0 := by
  let E := tensorOverUnitIso (sheafHomSpace Y.toRingedSpace F G) P V e
  let A := op (Over.mk (homOfLE hUV))
  let a : (sheafHomSpace Y.toRingedSpace F G).val.obj (op U) := E.hom.val.app A t
  have ha (W : Y.Opens) (hWU : W ≤ U) (hWr : W ≤ Y.basicOpen r) :
      (sheafHomSpace Y.toRingedSpace F G).val.map (homOfLE hWU).op a = 0 := by
    have htw := map_eq_zero_of_map_comp_eq_zero _ _ (homOfLE hWr).op (homOfLE hWU).op ht
    have hn := PresheafOfModules.naturality_apply E.hom.val
      (op (Over.homMk (homOfLE hWU) :
        Over.mk (homOfLE (hWU.trans hUV)) ⟶ Over.mk (homOfLE hUV))) t
    refine hn.symm.trans ?_
    refine Eq.trans (congrArg
      ((E.hom.val.app (op (Over.mk (homOfLE (hWU.trans hUV))))).hom) htw) ?_
    exact map_zero _
  obtain ⟨N, hz⟩ := exists_pow_smul_homSection_eq_zero q hU hUq r a ha
  have hiso : IsIso (E.hom.val.app A) :=
    ((PresheafOfModules.evaluation _ A).mapIso
      ((_root_.SheafOfModules.forget _).mapIso E)).isIso_hom
  have h0 : (E.hom.val.app A).hom (0 : _) = 0 := map_zero _
  have h1 := (LinearMap.map_smul ((E.hom.val.app A)).hom (r ^ N) t).trans hz
  exact ⟨N, (ConcreteCategory.bijective_of_isIso (E.hom.val.app A)).injective
    (h1.trans h0.symm)⟩

/-- **Functoriality of the restriction maps.** A global section of a sheaf of modules which
restricts to zero on an open `V` restricts to zero on `X.basicOpen r`, for a local equation `r`
on an open `W` whose basic open is contained in `V`; the restriction is read as the restriction
along `X.basicOpen r ≤ W` of the restriction to `W`, which is the shape the local statement
consumes.

Stated for a variable sheaf of modules so that the module it is applied to -- a tensor product of
an internal Hom sheaf with a twist, whose spelling is four lines long -- occurs once rather than
three times at the point of use. That matters: heartbeats are counted cumulatively over a
declaration, and the twisted section's local annihilator exceeds the budget only in total. -/
private lemma map_basicOpen_map_terminal_eq_zero
    (T : SheafOfModules.{u} (TensorSheafification.structureSheaf (sectionSiteRing X)
      (sectionSiteSheaf X)))
    {W : X.Opens} (r : (sectionSiteRing X).obj (op W))
    {V : Opens X.toRingedSpace.toPresheafedSpace} (hr : X.basicOpen r ≤ V)
    (t : T.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hv : T.val.map (terminal.from V).op t = 0) :
    T.val.map (homOfLE (X.basicOpen_le r)).op (T.val.map (terminal.from W).op t) = 0 := by
  rw [← PresheafOfModules.map_comp_apply]
  exact map_eq_zero_of_map_comp_eq_zero T.val _ (homOfLE hr).op _ hv

/-- **The affine open on which the argument is carried out.** Around every point there is an
affine open `W` inside a given neighbourhood `Z` of the point, contained in an open `V` on which
`L^{⊗ n}` is isomorphic to the structure sheaf, and carrying a local equation for `s`: a frame
of `L` over `W` writes `s|_W = r · l`, and `X.basicOpen r` lies inside the open where `s` does
not vanish.

Stated separately from the annihilator below for the reason recorded on
`Stacks.SheafOfModules.map_basicOpen_map_terminal_eq_zero`: heartbeats are counted cumulatively
over a declaration, and choosing this open is what the annihilator has no budget left for. No
tensor product of an internal Hom sheaf occurs here, only the twist itself. -/
private lemma exists_isAffineOpen_localEquation_and_trivialization (n : ℕ) (s : L.sections)
    {x : X} (Z : X.Opens) (hxZ : x ∈ Z) :
    ∃ (W V : X.Opens) (r : (sectionSiteRing X).obj (op W)) (l : L.val.obj (op W)),
      x ∈ W ∧ IsAffineOpen W ∧ W ≤ Z ∧ W ≤ V ∧ s.eval (op W) = r • l ∧
        X.basicOpen r ≤ nonvanishingOpen L s ∧
        Nonempty ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X)
            L (n : ℤ)).over V ≅
          _root_.SheafOfModules.unit ((structureSheafRing X.toRingedSpace).over V)) := by
  obtain ⟨W₀, hxW₀, b₀, hb₀⟩ := exists_bijective_smul_of_isInvertible L x
  have hPinv : IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) :=
    TensorPower.isInvertible_tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)
  obtain ⟨V, hxV, ⟨eP⟩⟩ := exists_mem_over_iso_unit
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) x
  obtain ⟨W, hWaff, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ W₀ ⊓ V ⊓ Z from ⟨⟨hxW₀, hxV⟩, hxZ⟩)
  have hWW₀ : W ≤ W₀ := fun z hz => (hWsub hz).1.1
  have hWV : W ≤ V := fun z hz => (hWsub hz).1.2
  have hWZ : W ≤ Z := fun z hz => (hWsub hz).2
  obtain ⟨r, l, hs, hr⟩ := exists_scalar_section_of_generator L s
    (generatorRestrict L hWW₀ ⟨b₀, hb₀⟩)
  exact ⟨W, V, r, l, hxW, hWaff, hWZ, hWV, hs, hr, ⟨eP⟩⟩

/-- **The local annihilator of a twisted section of the internal Hom sheaf.** Let `ℱ` and `𝒢` be
quasi-coherent `𝒪_X`-modules with `ℱ` of finite type and let `s` be a global section of an
invertible module `L`. A global section `t` of `ℋom(ℱ, 𝒢) ⊗ L^{⊗ n}` which vanishes on `X_s` is
annihilated near every point by a power of a local equation for `s`. -/
theorem exists_pow_smul_internalHomTwist_restrict_eq_zero
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFiniteType]
    (s : L.sections) (n : ℕ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨sectionSiteRing X, X.toRingedSpace.IsSheaf⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hv : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨sectionSiteRing X, X.toRingedSpace.IsSheaf⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op t = 0)
    (x : X) :
    ∃ (e : ℕ) (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U))
        (l : L.val.obj (op U)), x ∈ U ∧ s.eval (op U) = r • l ∧
      r ^ e • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨sectionSiteRing X, X.toRingedSpace.IsSheaf⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from U).op t = 0 := by
  obtain ⟨q⟩ := nonempty_localGenerators F x
  obtain ⟨W, V', r, l, hxW, hWaff, hWq, hWV', hs, hr, ⟨eP⟩⟩ :=
    exists_isAffineOpen_localEquation_and_trivialization X L n s q.nhd q.mem_nhd
  have htr := map_basicOpen_map_terminal_eq_zero X _ r hr t hv
  obtain ⟨e, he⟩ := exists_pow_smul_tensorHomSection_eq_zero (F := F) (G := G)
    (P := TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    q hWaff hWq hWV' eP r _ htr
  exact ⟨e, W, r, l, hxW, hs, he⟩

end TwistedAnnihilator

end Stacks.SheafOfModules

end
