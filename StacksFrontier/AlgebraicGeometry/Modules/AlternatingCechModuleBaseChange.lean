module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseRing
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleSectionsBaseChange

/-!
# Base change for the Čech complexes of a sheaf of modules

Let `φ : A →+* A'` be a ring map, let `f : X ⟶ Spec A` be a separated morphism, let
`f' : X' ⟶ Spec A'` and `g : X' ⟶ X` make `X'` the base change of `X` along `Spec A' → Spec A`,
and let `F` be a quasi-coherent `𝒪_X`-module. For a finite family `U : I → X.Opens` of affine
opens and the inverse-image family `U' i = g ⁻¹ᵁ U (e i)` on `X'`, this file identifies the
extension of scalars along `φ` of the two Čech complexes of `A`-modules of
`StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex` with the corresponding Čech
complexes of `g^*F` over `A'`, compatibly with the canonical alternating-to-usual inclusion.

## Main definitions

* `Stacks.Cech.pullbackSections` is in the imported sections file; here
  `Stacks.Cech.cochainBaseChange` is the induced comparison on Čech cochains: apply the
  canonical comparison on sections in each tuple, after reindexing the tuple by `e` and
  restricting along the identification `inter U' i = g ⁻¹ᵁ inter U (e ∘ i)`.
* `Stacks.Cech.cochainBaseChangeₗ` and `Stacks.Cech.alternatingCochainBaseChangeₗ` are that
  comparison as a map linear over the base ring `A`, on all cochains and on the alternating
  cochains.
* `Stacks.Cech.cechModuleComplexBaseChangeIso` and
  `Stacks.Cech.alternatingCechModuleComplexBaseChangeIso` are the resulting isomorphisms of
  complexes of `A'`-modules.
* `Stacks.Cech.CechBaseChangeData` packages the two isomorphisms together with the compatibility
  with the canonical inclusion, and `Stacks.Cech.cechBaseChangeData` constructs it.
* `Stacks.Cech.sectionsRestrₗ` and `Stacks.Cech.sectionsCongrₗ` are restriction of sections as
  a map, resp. an equivalence, linear over the base ring.
* `Stacks.Cech.tupleEquiv` and `Stacks.Cech.ordIndexEquiv` reindex tuples, resp. strictly
  increasing tuples, of indices along `e`.
* `Stacks.Cech.opensRange_eq_preimage_of_isPullback`: the base change of an open immersion has
  as its range the preimage of the range, which turns a cartesian square of affine open covers
  into the hypothesis `U' i = g ⁻¹ᵁ U (e i)`.

## Main results

* `Stacks.Cech.isBaseChange_pi`: base change commutes with finite products.
* `Stacks.Cech.preimage_iInf`: the preimage of a finite intersection of opens is the
  intersection of the preimages. Mathlib has `TopologicalSpace.Opens.map_iSup` but no `iInf`
  counterpart, and the finiteness hypothesis is genuinely needed.
* `Stacks.Cech.cochainBaseChange_cechD`, `Stacks.Cech.cochainBaseChange_isAlternating` and
  `Stacks.Cech.cochainBaseChange_smul`: the comparison is a morphism of complexes, carries
  alternating cochains to alternating cochains, and is semilinear over `φ`.
* `Stacks.Cech.isBaseChange_pullbackSectionsBaseₗ`: over an affine open the sections of the
  pullback are the base change of the sections *along `φ`* — the combination of the
  `Γ(X, W)`-level statement of the imported sections file with the pushout square of the
  structure sheaves.
* `Stacks.Cech.isBaseChange_cochainBaseChangeₗ` and
  `Stacks.Cech.isBaseChange_alternatingCochainBaseChangeₗ`: the comparison is bijective in every
  degree.
* `Stacks.Cech.baseChangeIso_inclusion_commutes`: base change preserves the canonical
  alternating-to-usual Čech inclusion.

## Implementation notes

**Everything is the canonical comparison, and that is what makes the proof possible.** The
degreewise comparison is built from the component of the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, so its compatibility with
every restriction map is naturality of a morphism of sheaves and needs no proof. Commutation
with the Čech differential, invariance of the alternating conditions and compatibility with the
canonical inclusion are then all consequences of that one naturality; only *bijectivity* uses
quasi-coherence, affineness and the cartesian square. An arbitrary isomorphism of sections would
not commute with the differentials, so no non-canonical comparison can be used here.

**Bijectivity is reduced to one affine open by two finite-product arguments.** In every degree
the Čech cochains are, definitionally, a finite product of modules of sections — over all tuples
for the usual complex, and over the *strictly increasing* tuples for the alternating one, via
`Stacks.Cech.ordLinearEquiv`, which is the `A`-linear form of Stacks 01FJ. So
`Stacks.Cech.isBaseChange_pi` plus a reindexing along `e` reduces both statements to the single
affine open `CechCochains.inter U (e ∘ i)`, which is affine by `Stacks.Cech.inter_isAffineOpen`.
The alternating submodule is *not* a direct summand — antisymmetrisation would need `p!`
invertible — so its base change is not read off the product directly; the ordered description is
what replaces that.

**The linear order on `I'` is pulled back from `I`.** Neither statement mentions an order, so
both are chosen inside the proof: `linearOrderOfSTO WellOrderingRel` on `I` and
`LinearOrder.lift' e e.injective` on `I'`, which makes `e` an order isomorphism and hence
`Stacks.Cech.ordIndexEquiv` available.

**Spelling discipline around `ModuleCat.extendScalars`.** With `Algebra A A'` taken to be
`φ.toAlgebra`, `(ModuleCat.extendScalars φ).obj M` *is* `ModuleCat.of A' (A' ⊗[A] M)`, so an
`IsBaseChange` equivalence can be ascribed directly as the degreewise isomorphism. The object
`(((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).X p` is however only
definitionally — not syntactically — `(ModuleCat.extendScalars φ).obj (K.X p)`, and `rw`/`simp`
refuse any goal mixing the two. Each commutation is therefore stated at the *morphism* level in
the unmixed spelling and discharged with `Eq.trans`/`congrArg`/`exact`, which tolerate defeq;
the degreewise comparisons are pinned by `..._hom_one_tmul`, proved from
`IsBaseChange.equiv_tmul`, and `ModuleCat.ExtendScalars.hom_ext` reduces every morphism identity
out of an extension of scalars to its values on `1 ⊗ₜ s`.

**`Stacks.Cech.restr_self` is public although it is only used in proofs**, because a public
definition cannot reference a `private` declaration under the module system and
`Stacks.Cech.sectionsCongrₗ` needs it.

**No `@[stacks]` attribute.** Stacks 01FH already has its carriers for the two complexes and
their inclusion. Stacks 01XL is the computation of `Rf_*F` by this complex, which is not proved
here, and the base-change statement for `H^m` of Stacks 08FX is a different assertion. The
content here is the auxiliary extension-of-scalars comparison that such a computation consumes.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

/-! ### Base change and finite products -/

/-- **Base change commutes with finite products.** -/
theorem isBaseChange_pi {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {ι : Type u} [Finite ι] (M : ι → Type u) (N : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] [∀ i, Module A' (N i)]
    [∀ i, IsScalarTower A A' (N i)]
    (c : ∀ i, M i →ₗ[A] N i) (hc : ∀ i, IsBaseChange A' (c i)) :
    IsBaseChange A' (LinearMap.pi fun i ↦ (c i).comp (LinearMap.proj i)) := by
  classical
  let _ := Fintype.ofFinite ι
  refine IsBaseChange.of_equiv
    (TensorProduct.piRight A A' A' M ≪≫ₗ LinearEquiv.piCongrRight fun i ↦ (hc i).equiv)
    fun x ↦ ?_
  funext i
  simp only [LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply, IsBaseChange.equiv_tmul,
    one_smul, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]

/-! ### Preimages of the intersections of a family of opens -/

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The preimage of a finite intersection of opens is the intersection of the preimages. -/
theorem preimage_iInf {ι : Type*} [Finite ι] (V : ι → X.Opens) :
    g ⁻¹ᵁ (⨅ k, V k) = ⨅ k, g ⁻¹ᵁ V k := by
  refine TopologicalSpace.Opens.ext ?_
  simp only [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]

variable {I I' : Type u} (U : I → X.Opens) (U' : I' → X'.Opens) (e : I' ≃ I)

/-- If each `U' i` is the preimage of `U (e i)`, then the same holds for the intersections
over a tuple of indices. -/
theorem inter_eq_preimage (hU' : ∀ i, U' i = g ⁻¹ᵁ U (e i)) {p : ℕ} (i : Fin p → I') :
    CechCochains.inter U' i = g ⁻¹ᵁ CechCochains.inter U (e ∘ i) := by
  simp only [CechCochains.inter, hU', preimage_iInf]
  rfl

/-! ### The comparison on Čech cochains -/

variable (F : X.Modules) (hU' : ∀ i, U' i = g ⁻¹ᵁ U (e i))

/-- The canonical comparison on sections is compatible with every restriction morphism of the
poset of opens, not only with the ones spelled `homOfLE`. -/
theorem map_comp_pullbackSections' {V W : X.Opens} (i : V ⟶ W) :
    F.presheaf.map i.op ≫ pullbackSections g F V =
      pullbackSections g F W ≫ ((Scheme.Modules.pullback g).obj F).presheaf.map
        ((Opens.map g.base).map i).op :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).mapPresheaf.naturality i.op

/-- The elementwise form of `Stacks.Cech.map_comp_pullbackSections'`, with the restriction on
the target spelled by an arbitrary inequality of opens. -/
theorem pullbackSections_restr {V W : X.Opens} (h : V ≤ W) {V' : X'.Opens}
    (h' : V' ≤ g ⁻¹ᵁ W) (hV' : V' ≤ g ⁻¹ᵁ V) (s : Γ(F, W)) :
    CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf hV'
        (pullbackSections g F V (CechCochains.restr F.presheaf h s)) =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf h'
        (pullbackSections g F W s) := by
  have hnat := congr($(map_comp_pullbackSections' g F (homOfLE h)) s)
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  show CechCochains.restr _ hV' (pullbackSections g F V (F.presheaf.map (homOfLE h).op s)) = _
  rw [hnat]
  show (((Scheme.Modules.pullback g).obj F).presheaf.map (homOfLE hV').op) _ = _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- The canonical comparison on Čech cochains: apply the canonical comparison on sections in
each tuple, after reindexing the tuple by `e` and restricting along the identification of the
intersection with the preimage of the intersection. -/
def cochainBaseChange (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    CechCochains.Cochain U' ((Scheme.Modules.pullback g).obj F).presheaf p := fun i ↦
  CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
    (inter_eq_preimage g U U' e hU' i).le
    ((pullbackSections g F (CechCochains.inter U (e ∘ i))) (s (e ∘ i)))

/-- The value of the comparison on Čech cochains at a tuple. -/
private theorem cochainBaseChange_apply (p : ℕ) (s : CechCochains.Cochain U F.presheaf p)
    (i : Fin (p + 1) → I') :
    cochainBaseChange g U U' e F hU' p s i =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
        (inter_eq_preimage g U U' e hU' i).le
        ((pullbackSections g F (CechCochains.inter U (e ∘ i))) (s (e ∘ i))) := rfl

/-- The comparison on Čech cochains is additive. -/
theorem cochainBaseChange_add (p : ℕ) (s t : CechCochains.Cochain U F.presheaf p) :
    cochainBaseChange g U U' e F hU' p (s + t) =
      cochainBaseChange g U U' e F hU' p s + cochainBaseChange g U U' e F hU' p t := by
  funext i
  simp only [cochainBaseChange, CechCochains.Cochain.add_apply, map_add]

/-- The comparison on Čech cochains sends zero to zero. -/
theorem cochainBaseChange_zero (p : ℕ) :
    cochainBaseChange g U U' e F hU' p 0 = 0 := by
  funext i
  simp only [cochainBaseChange, CechCochains.Cochain.zero_apply, map_zero]

/-- The value of the Čech differential at a tuple. -/
private theorem cechD_apply {Y : TopCat} {J : Type*} (V : J → Opens Y)
    (ℱ : TopCat.Presheaf Ab Y) (p : ℕ) (s : CechCochains.Cochain V ℱ p) (i : Fin (p + 2) → J) :
    CechCochains.cechD V ℱ p s i =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr ℱ (CechCochains.inter_le_omit V i j) (s (i ∘ j.succAbove)) := rfl

/-- The permutation identification is the restriction along the corresponding equality. -/
private theorem permIso_eq_restr {Y : TopCat} {J : Type*} (V : J → Opens Y)
    (ℱ : TopCat.Presheaf Ab Y) {p : ℕ} (i : Fin (p + 1) → J) (σ : Equiv.Perm (Fin (p + 1)))
    (x : (ℱ.obj (op (CechCochains.inter V i)) : Type _)) :
    CechCochains.permIso V ℱ i σ x =
      CechCochains.restr ℱ (CechCochains.inter_comp_perm V i σ).le x := by
  unfold CechCochains.permIso CechCochains.restr
  rw [Subsingleton.elim (eqToHom (by rw [CechCochains.inter_comp_perm V i σ]))
    (homOfLE (CechCochains.inter_comp_perm V i σ).le)]

/-- **The comparison on Čech cochains is a morphism of complexes.** -/
theorem cochainBaseChange_cechD (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    CechCochains.cechD U' ((Scheme.Modules.pullback g).obj F).presheaf p
        (cochainBaseChange g U U' e F hU' p s) =
      cochainBaseChange g U U' e F hU' (p + 1) (CechCochains.cechD U F.presheaf p s) := by
  funext i
  rw [cechD_apply, cochainBaseChange_apply, cechD_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cochainBaseChange_apply, CechCochains.restr_restr, map_zsmul, map_zsmul]
  congr 1
  exact (pullbackSections_restr g F (CechCochains.inter_le_omit U (e ∘ i) j) _ _
    (s (e ∘ (i ∘ j.succAbove)))).symm

/-- **The comparison on Čech cochains carries alternating cochains to alternating
cochains.** -/
theorem cochainBaseChange_isAlternating (p : ℕ) (s : CechCochains.Cochain U F.presheaf p)
    (hs : CechCochains.IsAlternating U F.presheaf s) :
    CechCochains.IsAlternating U' ((Scheme.Modules.pullback g).obj F).presheaf
      (cochainBaseChange g U U' e F hU' p s) := by
  refine ⟨fun i hi ↦ ?_, fun i a b hab ↦ ?_⟩
  · have : ¬ Function.Injective (e ∘ i) := fun hinj ↦ hi hinj.of_comp
    simp only [cochainBaseChange, hs.1 _ this, map_zero]
  · have key : s (e ∘ i ∘ Equiv.swap a b) = -CechCochains.restr F.presheaf
        (CechCochains.inter_comp_perm U (e ∘ i) (Equiv.swap a b)).le (s (e ∘ i)) :=
      (hs.2 (e ∘ i) a b hab).trans (by rw [permIso_eq_restr])
    rw [cochainBaseChange_apply, cochainBaseChange_apply, permIso_eq_restr,
      CechCochains.restr_restr, key, map_neg, map_neg]
    congr 1
    exact pullbackSections_restr g F (CechCochains.inter_comp_perm U (e ∘ i) (Equiv.swap a b)).le
      _ _ (s (e ∘ i))

/-! ### Semilinearity over the base rings -/

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A'))

/-- **The comparison on Čech cochains is semilinear over `φ`.** -/
theorem cochainBaseChange_smul
    (hbase : ∀ W : X.Opens,
      baseRingHom f W ≫ g.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g ⁻¹ᵁ W))
    (p : ℕ) (a : A) (s : CechCochains.Cochain U F.presheaf p) :
    letI := cochainModule f U F p
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    cochainBaseChange g U U' e F hU' p (a • s) =
      φ a • cochainBaseChange g U U' e F hU' p s := by
  let _ := cochainModule f U F p
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  funext i
  rw [cochain_smul_apply]
  rw [cochainBaseChange_apply, cochainBaseChange_apply, cochain_smul_apply, pullbackSections_smul]
  have hb := congr($(hbase (CechCochains.inter U (e ∘ i))).hom a)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hb
  show ((Scheme.Modules.pullback g).obj F).presheaf.map
      (homOfLE (inter_eq_preimage g U U' e hU' i).le).op (_ • _) = _
  rw [show (g.app (CechCochains.inter U (e ∘ i))).hom
      ((baseRingHom f (CechCochains.inter U (e ∘ i))).hom a) =
      (baseRingHom f' (g ⁻¹ᵁ CechCochains.inter U (e ∘ i))).hom (φ a) from hb,
    Scheme.Modules.map_smul, map_baseRingHom_apply]
  rfl

/-! ### The comparison on sections of an affine open as a base change over the base ring -/

/-- The `A`-module structure on the sections of the pullback, through `φ` and the structural
map of `f'`. -/
@[instance_reducible]
def baseSectionsModule (W' : X'.Opens) :
    Module A Γ((Scheme.Modules.pullback g).obj F, W') :=
  letI := sectionsModule f' ((Scheme.Modules.pullback g).obj F) W'
  Module.compHom _ φ

/-- The scalar tower `A → A' → Γ(g^*F, W')`. -/
theorem isScalarTowerBaseSections (W' : X'.Opens) :
    letI : Algebra A A' := φ.toAlgebra
    letI := sectionsModule f' ((Scheme.Modules.pullback g).obj F) W'
    letI := baseSectionsModule g F φ f' W'
    IsScalarTower A A' Γ((Scheme.Modules.pullback g).obj F, W') :=
  let _ : Algebra A A' := φ.toAlgebra
  let _ := sectionsModule f' ((Scheme.Modules.pullback g).obj F) W'
  let _ := baseSectionsModule g F φ f' W'
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable (hbase : ∀ W : X.Opens,
  baseRingHom f W ≫ g.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g ⁻¹ᵁ W))

/-- The canonical comparison on sections, as a map linear over the base ring `A`. -/
def pullbackSectionsBaseₗ (W : X.Opens) :
    letI := sectionsModule f F W
    letI := baseSectionsModule g F φ f' (g ⁻¹ᵁ W)
    Γ(F, W) →ₗ[A] Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
  letI := sectionsModule f F W
  letI := baseSectionsModule g F φ f' (g ⁻¹ᵁ W)
  { toFun := pullbackSections g F W
    map_add' := map_add _
    map_smul' := fun a s ↦ by
      have hb := congr($(hbase W).hom a)
      rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hb
      change pullbackSections g F W ((baseRingHom f W).hom a • s) =
        (baseRingHom f' (g ⁻¹ᵁ W)).hom (φ a) • pullbackSections g F W s
      rw [pullbackSections_smul]
      exact congrArg (· • pullbackSections g F W s) hb }

/-- **The sections of the pullback of a quasi-coherent module over an affine open are the base
change of the sections along `φ`.** -/
theorem isBaseChange_pullbackSectionsBaseₗ [F.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen (g ⁻¹ᵁ W))
    (hpush : IsPushout (baseRingHom f W) (CommRingCat.ofHom φ)
      (g.app W) (baseRingHom f' (g ⁻¹ᵁ W))) :
    letI : Algebra A A' := φ.toAlgebra
    letI := sectionsModule f F W
    letI := sectionsModule f' ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ W)
    letI := baseSectionsModule g F φ f' (g ⁻¹ᵁ W)
    letI := isScalarTowerBaseSections g F φ f' (g ⁻¹ᵁ W)
    IsBaseChange A' (pullbackSectionsBaseₗ g F φ f f' hbase W) := by
  let _ : Algebra A A' := φ.toAlgebra
  let _ := sectionsModule f F W
  let _ := sectionsModule f' ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ W)
  let _ := baseSectionsModule g F φ f' (g ⁻¹ᵁ W)
  let _ := isScalarTowerBaseSections g F φ f' (g ⁻¹ᵁ W)
  let _ : Algebra A Γ(X, W) := baseAlgebra f W
  let _ : Algebra A' Γ(X', g ⁻¹ᵁ W) := baseAlgebra f' (g ⁻¹ᵁ W)
  let _ : Algebra Γ(X, W) Γ(X', g ⁻¹ᵁ W) := algebraPullbackSections g W
  let _ : Algebra A Γ(X', g ⁻¹ᵁ W) := ((g.app W).hom.comp (baseRingHom f W).hom).toAlgebra
  let _ := modulePullbackSections g F W
  have hw : ((g.app W).hom.comp (baseRingHom f W).hom) =
      ((baseRingHom f' (g ⁻¹ᵁ W)).hom.comp φ) := by
    have := congrArg CommRingCat.Hom.hom hpush.w
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at this
  have _ : IsScalarTower A Γ(X, W) Γ(X', g ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower A A' Γ(X', g ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' hw
  have _ : IsScalarTower A Γ(X, W) Γ(F, W) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower A' Γ(X', g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower Γ(X, W) Γ(X', g ⁻¹ᵁ W)
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower A Γ(X, W) Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      show ((g.app W).hom ((baseRingHom f W).hom a)) • x =
        ((baseRingHom f' (g ⁻¹ᵁ W)).hom (φ a)) • x
      exact congrArg (· • x) (DFunLike.congr_fun hw a)
  have hps : Algebra.IsPushout A Γ(X, W) A' Γ(X', g ⁻¹ᵁ W) := by
    refine (CommRingCat.isPushout_iff_isPushout (R := A) (R' := Γ(X, W)) (S := A')
      (S' := Γ(X', g ⁻¹ᵁ W))).mp ?_
    exact hpush
  have _ : Algebra.IsPushout A A' Γ(X, W) Γ(X', g ⁻¹ᵁ W) := hps.symm
  exact isBaseChange_restrictScalars_of_isPushout (pullbackSectionsₗ g F W)
    (isBaseChange_pullbackSectionsₗ g F hW hW')

/-! ### The comparison on Čech cochains as a base change over the base ring -/

/-- Restriction along the identity inequality is the identity. -/
theorem restr_self {Y : TopCat} (ℱ : TopCat.Presheaf Ab Y) {V : Opens Y} (h : V ≤ V)
    (x : (ℱ.obj (op V) : Type _)) : CechCochains.restr ℱ h x = x := by
  unfold CechCochains.restr
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, ℱ.map_id]
  rfl

/-- Restriction of sections, as a map linear over the base ring. -/
def sectionsRestrₗ (G : X'.Modules) {V W : X'.Opens} (hWV : W ≤ V) :
    letI := sectionsModule f' G V
    letI := sectionsModule f' G W
    Γ(G, V) →ₗ[A'] Γ(G, W) :=
  letI := sectionsModule f' G V
  letI := sectionsModule f' G W
  { toFun := CechCochains.restr G.presheaf hWV
    map_add' := map_add _
    map_smul' := fun a x ↦ by
      change (G.presheaf.map (homOfLE hWV).op) ((baseRingHom f' V).hom a • x) = _
      rw [Scheme.Modules.map_smul, map_baseRingHom_apply]
      rfl }

/-- Restriction along an equality of opens, as a linear equivalence over the base ring. -/
def sectionsCongrₗ (G : X'.Modules) {V W : X'.Opens} (h : V = W) :
    letI := sectionsModule f' G V
    letI := sectionsModule f' G W
    Γ(G, V) ≃ₗ[A'] Γ(G, W) :=
  letI := sectionsModule f' G V
  letI := sectionsModule f' G W
  LinearEquiv.ofLinearMap (sectionsRestrₗ f' G h.ge) (sectionsRestrₗ f' G h.le)
    (LinearMap.ext fun x ↦
      ((CechCochains.restr_restr G.presheaf h.le h.ge x).trans (restr_self G.presheaf _ x)))
    (LinearMap.ext fun x ↦
      ((CechCochains.restr_restr G.presheaf h.ge h.le x).trans (restr_self G.presheaf _ x)))

/-- The linear equivalence of `Stacks.Cech.sectionsCongrₗ` is the restriction map. -/
theorem sectionsCongrₗ_apply (G : X'.Modules) {V W : X'.Opens} (h : V = W)
    (x : Γ(G, V)) :
    sectionsCongrₗ f' G h x = CechCochains.restr G.presheaf h.ge x := rfl

/-- The `A`-module structure on the Čech cochains of the pullback, through `φ`. -/
@[instance_reducible]
def baseCochainModule (p : ℕ) :
    Module A (CechCochains.Cochain U' ((Scheme.Modules.pullback g).obj F).presheaf p) :=
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  Module.compHom _ φ

/-- The scalar tower `A → A' → Č^p` on the Čech cochains of the pullback. -/
theorem isScalarTowerBaseCochain (p : ℕ) :
    letI : Algebra A A' := φ.toAlgebra
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    letI := baseCochainModule g U' F φ f' p
    IsScalarTower A A' (CechCochains.Cochain U' ((Scheme.Modules.pullback g).obj F).presheaf p) :=
  let _ : Algebra A A' := φ.toAlgebra
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseCochainModule g U' F φ f' p
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The comparison on Čech cochains, as a map linear over the base ring `A`. -/
def cochainBaseChangeₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := baseCochainModule g U' F φ f' p
    CechCochains.Cochain U F.presheaf p →ₗ[A]
      CechCochains.Cochain U' ((Scheme.Modules.pullback g).obj F).presheaf p :=
  letI := cochainModule f U F p
  letI := baseCochainModule g U' F φ f' p
  { toFun := cochainBaseChange g U U' e F hU' p
    map_add' := cochainBaseChange_add g U U' e F hU' p
    map_smul' := fun a s ↦ cochainBaseChange_smul g U U' e F hU' φ f f' hbase p a s }

/-- The reindexing of a tuple of indices along `e`, as an equivalence. -/
def tupleEquiv (p : ℕ) : (Fin (p + 1) → I) ≃ (Fin (p + 1) → I') :=
  Equiv.arrowCongr (Equiv.refl _) e.symm

/-- **The Čech cochains of the pullback are the base change of the Čech cochains.** -/
theorem isBaseChange_cochainBaseChangeₗ [Finite I] [IsSeparated f] [F.IsQuasicoherent]
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hUaff : ∀ i, IsAffineOpen (U i)) (p : ℕ) :
    letI : Algebra A A' := φ.toAlgebra
    letI := cochainModule f U F p
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    letI := baseCochainModule g U' F φ f' p
    letI := isScalarTowerBaseCochain g U' F φ f' p
    IsBaseChange A' (cochainBaseChangeₗ g U U' e F hU' φ f f' hbase p) := by
  let _ : Algebra A A' := φ.toAlgebra
  let _ : ∀ W : X.Opens, Module A Γ(F, W) := fun _ ↦ sectionsModule f F _
  let _ : ∀ W' : X'.Opens, Module A' Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ sectionsModule f' _ _
  let _ : ∀ W' : X'.Opens, Module A Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ baseSectionsModule g F φ f' _
  let _ := cochainModule f U F p
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseCochainModule g U' F φ f' p
  let _ := isScalarTowerBaseCochain g U' F φ f' p
  have _ : ∀ W' : X'.Opens, IsScalarTower A A' Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ isScalarTowerBaseSections g F φ f' _
  let c : ∀ j : Fin (p + 1) → I', Γ(F, CechCochains.inter U (e ∘ j)) →ₗ[A]
      Γ((Scheme.Modules.pullback g).obj F, CechCochains.inter U' j) := fun j ↦
    ((sectionsCongrₗ f' ((Scheme.Modules.pullback g).obj F)
      (inter_eq_preimage g U U' e hU' j).symm).restrictScalars A).toLinearMap.comp
      (pullbackSectionsBaseₗ g F φ f f' hbase (CechCochains.inter U (e ∘ j)))
  have hc : ∀ j, IsBaseChange A' (c j) := fun j ↦ by
    have hWaff : IsAffineOpen (CechCochains.inter U (e ∘ j)) := inter_isAffineOpen f U hUaff _
    have hkey := isBaseChange_pullbackSectionsBaseₗ g F φ f f' hbase hWaff
      (isAffineOpen_preimage_of_isPullback φ f f' g hsq hWaff)
      (isPushout_baseRingHom φ f f' g hsq hWaff)
    refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl A _)
      (sectionsCongrₗ f' ((Scheme.Modules.pullback g).obj F)
        (inter_eq_preimage g U U' e hU' j).symm) ?_).mp hkey
    rfl
  have _ : Finite I' := Finite.of_equiv I e.symm
  have hpi := isBaseChange_pi _ _ c hc
  refine (IsBaseChange.iff_of_equiv_comm
    (LinearEquiv.piCongrLeft' A (fun i : Fin (p + 1) → I ↦ Γ(F, CechCochains.inter U i))
      (tupleEquiv e p))
    (LinearEquiv.refl A'
      (CechCochains.Cochain U' ((Scheme.Modules.pullback g).obj F).presheaf p)) ?_).mpr hpi
  rfl

/-! ### The comparison on alternating Čech cochains -/

/-- The `A`-module structure on the alternating Čech cochains of the pullback, through `φ`. -/
@[instance_reducible]
def baseAlternatingModule (p : ℕ) :
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    Module A (alternatingSubmodule f' U' ((Scheme.Modules.pullback g).obj F) p) :=
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  Module.compHom _ φ

/-- The scalar tower `A → A' → Č_alt^p` on the alternating cochains of the pullback. -/
theorem isScalarTowerBaseAlternating (p : ℕ) :
    letI : Algebra A A' := φ.toAlgebra
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    letI := baseAlternatingModule g U' F φ f' p
    IsScalarTower A A' (alternatingSubmodule f' U' ((Scheme.Modules.pullback g).obj F) p) :=
  let _ : Algebra A A' := φ.toAlgebra
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseAlternatingModule g U' F φ f' p
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The comparison on alternating Čech cochains, as a map linear over the base ring `A`. -/
def alternatingCochainBaseChangeₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    letI := baseAlternatingModule g U' F φ f' p
    alternatingSubmodule f U F p →ₗ[A]
      alternatingSubmodule f' U' ((Scheme.Modules.pullback g).obj F) p :=
  letI := cochainModule f U F p
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  letI := baseAlternatingModule g U' F φ f' p
  { toFun := fun s ↦ ⟨cochainBaseChange g U U' e F hU' p s.1,
      cochainBaseChange_isAlternating g U U' e F hU' p s.1 s.2⟩
    map_add' := fun s t ↦ Subtype.ext (cochainBaseChange_add g U U' e F hU' p s.1 t.1)
    map_smul' := fun a s ↦
      Subtype.ext (cochainBaseChange_smul g U U' e F hU' φ f f' hbase p a s.1) }

/-! ### The base-change isomorphism of the usual Čech complex -/

variable [Finite I] [IsSeparated f] [F.IsQuasicoherent]
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- The degreewise base-change isomorphism for the usual Čech complex of `A`-modules. -/
def cechModuleObjBaseChangeIso (p : ℕ) :
    (ModuleCat.extendScalars φ).obj (cechModuleObj f U F p) ≅
      cechModuleObj f' U' ((Scheme.Modules.pullback g).obj F) p :=
  letI : Algebra A A' := φ.toAlgebra
  letI := cochainModule f U F p
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  letI := baseCochainModule g U' F φ f' p
  letI := isScalarTowerBaseCochain g U' F φ f' p
  (isBaseChange_cochainBaseChangeₗ g U U' e F hU' φ f f' hbase hsq hUaff p).equiv.toModuleIso

/-- On a cochain pulled back along the unit, the degreewise base-change isomorphism is the
comparison of Čech cochains. -/
theorem cechModuleObjBaseChangeIso_hom_one_tmul (p : ℕ)
    (s : CechCochains.Cochain U F.presheaf p) :
    letI : Algebra A A' := φ.toAlgebra
    letI := cochainModule f U F p
    (cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom
        ((1 : A') ⊗ₜ[A] s) =
      cochainBaseChange g U U' e F hU' p s :=
  let _ : Algebra A A' := φ.toAlgebra
  let _ := cochainModule f U F p
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseCochainModule g U' F φ f' p
  let _ := isScalarTowerBaseCochain g U' F φ f' p
  ((isBaseChange_cochainBaseChangeₗ g U U' e F hU' φ f f' hbase hsq hUaff p).equiv_tmul 1 s).trans
    (one_smul _ _)

/-- The degreewise base-change isomorphism commutes with the Čech differentials. -/
theorem cechModuleObjBaseChangeIso_comm (p : ℕ) :
    (cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom ≫
        cechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p =
      (ModuleCat.extendScalars φ).map (cechModuleDiff f U F p) ≫
        (cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff (p + 1)).hom := by
  refine ModuleCat.ExtendScalars.hom_ext fun s ↦ ?_
  show cechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p
      ((cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom
        ((1 : A') ⊗ₜ[A] s)) =
    (cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff (p + 1)).hom
      ((ModuleCat.extendScalars φ).map (cechModuleDiff f U F p) ((1 : A') ⊗ₜ[A] s))
  refine Eq.trans (congrArg (fun x ↦ cechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p x)
    (cechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU' φ f f' hbase hsq hUaff p s)) ?_
  refine Eq.trans (cochainBaseChange_cechD g U U' e F hU' p s) ?_
  exact (cechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU' φ f f' hbase hsq hUaff (p + 1)
    (CechCochains.cechD U F.presheaf p s)).symm

/-- **The base-change isomorphism of the usual Čech complex of `A`-modules.** -/
def cechModuleComplexBaseChangeIso :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex f U F) ≅
      cechModuleComplex f' U' ((Scheme.Modules.pullback g).obj F) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ cechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p) ?_
  rintro p q (rfl : p + 1 = q)
  rw [Functor.mapHomologicalComplex_obj_d, cechModuleComplex_d, cechModuleComplex_d]
  exact cechModuleObjBaseChangeIso_comm g U U' e F hU' φ f f' hbase hsq hUaff p

/-! ### The base-change isomorphism of the alternating Čech complex -/

/-- Reindexing strictly increasing tuples along an order isomorphism of index types. -/
def ordIndexEquiv {J J' : Type u} [LinearOrder J] [LinearOrder J'] (ε : J' ≃ J)
    (hε : StrictMono ε) (hε' : StrictMono ε.symm) (p : ℕ) :
    CechCochains.OrdIndex (I := J) p ≃ CechCochains.OrdIndex (I := J') p where
  toFun i := ⟨ε.symm ∘ i.1, hε'.comp i.2⟩
  invFun j := ⟨ε ∘ j.1, hε.comp j.2⟩
  left_inv i := Subtype.ext (funext fun k ↦ ε.apply_symm_apply (i.1 k))
  right_inv j := Subtype.ext (funext fun k ↦ ε.symm_apply_apply (j.1 k))

include hsq hUaff in
/-- **The alternating Čech cochains of the pullback are the base change of the alternating
Čech cochains.** -/
theorem isBaseChange_alternatingCochainBaseChangeₗ (p : ℕ) :
    letI : Algebra A A' := φ.toAlgebra
    letI := cochainModule f U F p
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    letI := baseAlternatingModule g U' F φ f' p
    letI := isScalarTowerBaseAlternating g U' F φ f' p
    IsBaseChange A' (alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase p) := by
  classical
  let _ : Algebra A A' := φ.toAlgebra
  let _ : ∀ W : X.Opens, Module A Γ(F, W) := fun _ ↦ sectionsModule f F _
  let _ : ∀ W' : X'.Opens, Module A' Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ sectionsModule f' _ _
  let _ : ∀ W' : X'.Opens, Module A Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ baseSectionsModule g F φ f' _
  have _ : ∀ W' : X'.Opens, IsScalarTower A A' Γ((Scheme.Modules.pullback g).obj F, W') :=
    fun _ ↦ isScalarTowerBaseSections g F φ f' _
  let _ := cochainModule f U F p
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseAlternatingModule g U' F φ f' p
  let _ := isScalarTowerBaseAlternating g U' F φ f' p
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder I' := LinearOrder.lift' e e.injective
  let _ := ordCochainModule f U F p
  let _ := ordCochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ : Module A (CechCochains.OrdCochain U' ((Scheme.Modules.pullback g).obj F).presheaf p) :=
    inferInstanceAs (Module A (∀ j : CechCochains.OrdIndex (I := I') p,
      Γ((Scheme.Modules.pullback g).obj F, CechCochains.inter U' j.1)))
  have _ : IsScalarTower A A'
      (CechCochains.OrdCochain U' ((Scheme.Modules.pullback g).obj F).presheaf p) :=
    inferInstanceAs (IsScalarTower A A' (∀ j : CechCochains.OrdIndex (I := I') p,
      Γ((Scheme.Modules.pullback g).obj F, CechCochains.inter U' j.1)))
  have hmono : StrictMono e := fun _ _ h ↦ h
  have hmono' : StrictMono e.symm := fun a b h ↦ by
    show e (e.symm a) < e (e.symm b)
    rwa [e.apply_symm_apply, e.apply_symm_apply]
  have _ : Finite I' := Finite.of_equiv I e.symm
  let c : ∀ j : CechCochains.OrdIndex (I := I') p, Γ(F, CechCochains.inter U (e ∘ j.1)) →ₗ[A]
      Γ((Scheme.Modules.pullback g).obj F, CechCochains.inter U' j.1) := fun j ↦
    ((sectionsCongrₗ f' ((Scheme.Modules.pullback g).obj F)
      (inter_eq_preimage g U U' e hU' j.1).symm).restrictScalars A).toLinearMap.comp
      (pullbackSectionsBaseₗ g F φ f f' hbase (CechCochains.inter U (e ∘ j.1)))
  have hc : ∀ j, IsBaseChange A' (c j) := fun j ↦ by
    have hWaff : IsAffineOpen (CechCochains.inter U (e ∘ j.1)) := inter_isAffineOpen f U hUaff _
    have hkey := isBaseChange_pullbackSectionsBaseₗ g F φ f f' hbase hWaff
      (isAffineOpen_preimage_of_isPullback φ f f' g hsq hWaff)
      (isPushout_baseRingHom φ f f' g hsq hWaff)
    refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl A _)
      (sectionsCongrₗ f' ((Scheme.Modules.pullback g).obj F)
        (inter_eq_preimage g U U' e hU' j.1).symm) ?_).mp hkey
    rfl
  refine (IsBaseChange.iff_of_equiv_comm
    (ordLinearEquiv f U F p ≪≫ₗ LinearEquiv.piCongrLeft' A
      (fun i : CechCochains.OrdIndex (I := I) p ↦ Γ(F, CechCochains.inter U i.1))
      (ordIndexEquiv e hmono hmono' p))
    (ordLinearEquiv f' U' ((Scheme.Modules.pullback g).obj F) p) ?_).mpr
    (isBaseChange_pi _ _ c hc)
  rfl

/-- The degreewise base-change isomorphism for the alternating Čech complex of `A`-modules. -/
def alternatingCechModuleObjBaseChangeIso (p : ℕ) :
    (ModuleCat.extendScalars φ).obj (alternatingCechModuleObj f U F p) ≅
      alternatingCechModuleObj f' U' ((Scheme.Modules.pullback g).obj F) p :=
  letI : Algebra A A' := φ.toAlgebra
  letI := cochainModule f U F p
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  letI := baseAlternatingModule g U' F φ f' p
  letI := isScalarTowerBaseAlternating g U' F φ f' p
  (isBaseChange_alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase hsq hUaff
    p).equiv.toModuleIso

/-- On an alternating cochain pulled back along the unit, the degreewise base-change
isomorphism is the comparison of alternating Čech cochains. -/
theorem alternatingCechModuleObjBaseChangeIso_hom_one_tmul (p : ℕ)
    (s : alternatingCechModuleObj f U F p) :
    letI : Algebra A A' := φ.toAlgebra
    (alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom
        ((1 : A') ⊗ₜ[A] s) =
      alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase p s :=
  let _ : Algebra A A' := φ.toAlgebra
  let _ := cochainModule f U F p
  let _ := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  let _ := baseAlternatingModule g U' F φ f' p
  let _ := isScalarTowerBaseAlternating g U' F φ f' p
  ((isBaseChange_alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase hsq hUaff
    p).equiv_tmul 1 s).trans (one_smul _ _)

/-- The degreewise base-change isomorphism commutes with the alternating Čech
differentials. -/
theorem alternatingCechModuleObjBaseChangeIso_comm (p : ℕ) :
    (alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom ≫
        alternatingCechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p =
      (ModuleCat.extendScalars φ).map (alternatingCechModuleDiff f U F p) ≫
        (alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff
          (p + 1)).hom := by
  refine ModuleCat.ExtendScalars.hom_ext fun s ↦ ?_
  show alternatingCechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p
      ((alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p).hom
        ((1 : A') ⊗ₜ[A] s)) =
    (alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff (p + 1)).hom
      ((ModuleCat.extendScalars φ).map (alternatingCechModuleDiff f U F p) ((1 : A') ⊗ₜ[A] s))
  have h2 : alternatingCechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p
        (alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase p s) =
      alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase (p + 1)
        (alternatingCechModuleD f U F p s) :=
    Subtype.ext (cochainBaseChange_cechD g U U' e F hU' p s.1)
  refine Eq.trans (congrArg
    (fun x ↦ alternatingCechModuleDiff f' U' ((Scheme.Modules.pullback g).obj F) p x)
    (alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU' φ f f' hbase hsq hUaff
      p s)) ?_
  refine h2.trans ?_
  exact (alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU' φ f f' hbase hsq hUaff
    (p + 1) (alternatingCechModuleD f U F p s)).symm

/-- **The base-change isomorphism of the alternating Čech complex of `A`-modules.** -/
def alternatingCechModuleComplexBaseChangeIso :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U F) ≅
      alternatingCechModuleComplex f' U' ((Scheme.Modules.pullback g).obj F) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ alternatingCechModuleObjBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff p) ?_
  rintro p q (rfl : p + 1 = q)
  rw [Functor.mapHomologicalComplex_obj_d, alternatingCechModuleComplex_d,
    alternatingCechModuleComplex_d]
  exact alternatingCechModuleObjBaseChangeIso_comm g U U' e F hU' φ f f' hbase hsq hUaff p

/-- **Base change preserves the canonical alternating-to-usual Čech comparison.** -/
theorem baseChangeIso_inclusion_commutes :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModuleComplex_inclusion f U F) ≫
      (cechModuleComplexBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff).hom =
    (alternatingCechModuleComplexBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff).hom ≫
      alternatingCechModuleComplex_inclusion f' U' ((Scheme.Modules.pullback g).obj F) := by
  refine HomologicalComplex.hom_ext _ _ (fun p ↦ ?_)
  refine ModuleCat.ExtendScalars.hom_ext fun s ↦ ?_
  show (cechModuleComplexBaseChangeIso g U U' e F hU' φ f f' hbase hsq hUaff).hom.f p
      ((ModuleCat.extendScalars φ).map (alternatingCechModuleSubtype f U F p)
        ((1 : A') ⊗ₜ[A] s)) =
    alternatingCechModuleSubtype f' U' ((Scheme.Modules.pullback g).obj F) p
      ((alternatingCechModuleComplexBaseChangeIso g U U' e F hU' φ f f' hbase hsq
        hUaff).hom.f p ((1 : A') ⊗ₜ[A] s))
  refine Eq.trans (cechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU' φ f f' hbase hsq hUaff
    p s.1) ?_
  exact congrArg Subtype.val (alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U U' e F hU'
    φ f f' hbase hsq hUaff p s).symm

end Stacks.Cech

namespace Stacks.Cech

/-! ### The base-change data of the Čech complexes -/

/-- **The base change of an open immersion has as its range the preimage of the range.** This
is what turns a cartesian square of covers into the hypothesis
`U' i = g ⁻¹ᵁ U (e i)` of `Stacks.Cech.cechBaseChangeData`. -/
theorem opensRange_eq_preimage_of_isPullback {Z Z' V V' : Scheme.{u}}
    {q : V' ⟶ V} {j' : V' ⟶ Z'} {j : V ⟶ Z} {g : Z' ⟶ Z}
    [IsOpenImmersion j'] [IsOpenImmersion j] (h : IsPullback q j' j g) :
    j'.opensRange = g ⁻¹ᵁ j.opensRange := by
  have key := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h ⊤
  rwa [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange] at key

/-- **The simultaneous base-change comparisons for the alternating and the usual Čech complex
of a sheaf of modules, including compatibility with their canonical inclusion.** -/
structure CechBaseChangeData {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
    (F : X.Modules) {I I' : Type u} (U : I → X.Opens) (U' : I' → X'.Opens) where
  /-- Extension of scalars of the alternating Čech complex is the alternating Čech complex of
  the inverse-image family. -/
  alternatingIso :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U F) ≅
      alternatingCechModuleComplex f' U' ((Scheme.Modules.pullback g).obj F)
  /-- The corresponding comparison for the usual Čech complex. -/
  usualIso :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex f U F) ≅
      cechModuleComplex f' U' ((Scheme.Modules.pullback g).obj F)
  /-- Base change preserves the canonical alternating-to-usual comparison. -/
  inclusion_commutes :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModuleComplex_inclusion f U F) ≫ usualIso.hom =
      alternatingIso.hom ≫
        alternatingCechModuleComplex_inclusion f' U' ((Scheme.Modules.pullback g).obj F)

/-- **For a separated morphism to an affine base and a quasi-coherent module, base change of a
finite family of affine opens carries the canonical Čech inclusion to the canonical inclusion
on the inverse-image family.** Separatedness makes finite intersections of affine opens affine,
so their sections commute with arbitrary base change. -/
def cechBaseChangeData {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f] (f' : X' ⟶ Spec (.of A'))
    (g : X' ⟶ X) (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (F : X.Modules) [F.IsQuasicoherent] {I I' : Type u} [Finite I]
    (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (U' : I' → X'.Opens)
    (e : I' ≃ I) (hU' : ∀ i, U' i = g ⁻¹ᵁ U (e i)) :
    CechBaseChangeData φ f f' g F U U' where
  alternatingIso := alternatingCechModuleComplexBaseChangeIso g U U' e F hU' φ f f'
    (fun W ↦ baseRingHom_comp_app φ f f' g hsq W) hsq hUaff
  usualIso := cechModuleComplexBaseChangeIso g U U' e F hU' φ f f'
    (fun W ↦ baseRingHom_comp_app φ f f' g hsq W) hsq hUaff
  inclusion_commutes := baseChangeIso_inclusion_commutes g U U' e F hU' φ f f'
    (fun W ↦ baseRingHom_comp_app φ f f' g hsq W) hsq hUaff

end Stacks.Cech

end

end
