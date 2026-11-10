module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelResidueFieldRigidity
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelStalkIdeal
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar

/-!
# The comorphism of a self-map carrying a natural isomorphism `g^* ≅ 𝟭`

Let `X` be a locally Noetherian scheme, let `g : X ⟶ X` be a self-map and suppose the ordinary
pullback along `g` is *naturally* isomorphic to the identity on the coherent `𝒪_X`-modules.  Then
for every closed point `x` fixed by `g` the comorphism `g^♯_x : 𝒪_{X,g x} ⟶ 𝒪_{X,x}` induces the
canonical identification of residue fields, and therefore

`Spec κ(x) ⟶ X` is unchanged by `g`.

## Main results

* `Stacks.Duality.exists_germ_eq_of_subsingleton` — on a one-point space every element of a stalk
  is the germ of a section over any neighbourhood of the point.
* `Stacks.Duality.exists_Γgerm_eq_pointTestModule` — the global sections of `𝒪_X/𝔪_y` exhaust its
  stalk at a closed point `y`.
* `Stacks.Duality.Γgerm_smul_congr_point` and `Stacks.Duality.Γgerm_ne_zero_congr_point` — a
  relation between germs of global sections, and the nonvanishing of such a germ, transport along
  an equality of points.
* `Stacks.Duality.exists_hom_unitModule_app_top_eq` — every global section of a module is the
  value at `1` of a morphism out of `𝒪_X`.
* `Stacks.Duality.exists_smul_unitApp_of_cyclic` and
  `Stacks.Duality.isUnit_of_extendScalars_iso` — a cyclic module stays cyclic after extension of
  scalars, and an isomorphism from such a base change to a free rank-one module carries `1 ⊗ e`
  to a unit multiple of the generator.
* `Stacks.Duality.lambdaIso` and `Stacks.Duality.kappaHom`, with their naturality — the
  comparison `Λ_ℱ : 𝒪_{X,x} ⊗_{𝒪_{X,g x}} ℱ_{g x} ≅ ℱ_x` of [Stacks, Tag 0098] composed with the
  given natural isomorphism, and its transpose `κ_ℱ`.
* `Stacks.Duality.kappaHom_Γgerm` — `κ_ℱ(s_{g x}) = v · s_x` for every global section `s` of `ℱ`,
  with `v` the unit `Stacks.Duality.natIsoUnitScalar`.
* `Stacks.Duality.residue_stalkMap_germ_eq_of_natIso` — `g^♯_x` induces the identity on `κ(x)`,
  germwise.
* `Stacks.Duality.fromSpecResidueField_comp_eq_of_natIso` — hence `Spec κ(x) ⟶ X` is unchanged
  by `g`.
* `Stacks.Duality.comp_fst_eq_id_of_representsIdentityOnPerfect` — under the hypotheses of
  [Stacks, Tag 0G0E] together with `K ≅ Rs_*𝒪_X` for a section `s` of `pr_2`, the morphism
  `pr_1 ∘ s` is the identity of `X`.
* `Stacks.Duality.iso_diagonalFourierMukaiKernel_of_exists_section` — under the hypotheses of
  [Stacks, Tag 0G0E], if `K ≅ Rs_*𝒪_X` for a section `s` of `pr_2`, then `K` is isomorphic to the
  diagonal kernel.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Germs on a one-point space -/

/-- **On a one-point space every element of a stalk is the germ of a section over any
neighbourhood of the point.** -/
theorem exists_germ_eq_of_subsingleton {Z : TopCat.{u}} [Subsingleton Z]
    (P : TopCat.Presheaf AddCommGrpCat.{u} Z) {V : Opens Z} {z : Z} (hz : z ∈ V)
    (t : ToType (TopCat.Presheaf.stalk P z)) :
    ∃ s : ToType (P.obj (Opposite.op V)), (P.germ V z hz) s = t := by
  obtain ⟨W, hzW, s, hs⟩ := TopCat.Presheaf.exists_germ_eq P t
  obtain rfl : W = V := by
    refine SetLike.coe_injective (Set.Subset.antisymm (fun w _ ↦ ?_) (fun w _ ↦ ?_))
    · rwa [Subsingleton.elim w z]
    · rwa [Subsingleton.elim w z]
  exact ⟨s, hs⟩

/-- A closed immersion whose image is a subsingleton has a one-point source. -/
theorem subsingleton_of_range_subsingleton {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hr : Set.Subsingleton (Set.range (ConcreteCategory.hom i.base))) :
    Subsingleton Z :=
  ⟨fun a b ↦ (IsClosedImmersion.isClosedEmbedding i).injective
    (hr (Set.mem_range_self a) (Set.mem_range_self b))⟩

/-! ### The global sections of the test module exhaust its stalk -/

/-- **The direct image of the structure sheaf of a one-point closed subscheme has global sections
exhausting its stalk.** -/
theorem exists_Γgerm_eq_pushforward_unit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Subsingleton Z] (z : Z)
    (t : ToType (TopCat.Presheaf.stalk
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).presheaf (i z))) :
    ∃ s : Γ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z), ⊤),
      (((Scheme.Modules.pushforward i).obj
        (Stacks.Ample.unitModule Z)).presheaf.germ ⊤ (i z) trivial) s = t := by
  obtain ⟨s, hs⟩ := exists_germ_eq_of_subsingleton
    (Stacks.Ample.unitModule Z).presheaf (V := i ⁻¹ᵁ (⊤ : X.Opens)) (z := z) trivial
    (Stacks.Chow.stalkPushforwardComparison i (Stacks.Ample.unitModule Z) z t)
  refine ⟨s, (Stacks.Chow.bijective_stalkPushforwardComparison i _ z
    (IsClosedImmersion.isClosedEmbedding i).isInducing).1 ?_⟩
  rwa [Stacks.Chow.stalkPushforwardComparison_germ i (Stacks.Ample.unitModule Z) z ⊤ trivial s]

/-- The closed subscheme cut out by the first power of the vanishing ideal sheaf of a closed
point is a one-point scheme. -/
theorem subsingleton_subscheme_pointTestModule {X : Scheme.{u}} (y : X)
    (hy : IsClosed ({y} : Set X)) :
    Subsingleton ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X)) ^ 1).subscheme) := by
  refine subsingleton_of_range_subsingleton
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)) ^ 1).subschemeι ?_
  have h1 : SheafOfModules.supp (pointTestModule y 1) =
      Set.range (ConcreteCategory.hom ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X)) ^ 1).subschemeι).base) :=
    Stacks.Chow.supp_pushforwardStructureSheaf _
  rw [← h1, supp_pointTestModule y hy one_ne_zero]
  exact Set.subsingleton_singleton

/-- **The global sections of `𝒪_X/𝔪_y` exhaust its stalk at the closed point `y`.** -/
theorem exists_Γgerm_eq_pointTestModule {X : Scheme.{u}} (y : X)
    (hy : IsClosed ({y} : Set X))
    (t : ToType (TopCat.Presheaf.stalk (pointTestModule y 1).presheaf y)) :
    ∃ s : Γ(pointTestModule y 1, ⊤),
      ((pointTestModule y 1).presheaf.Γgerm y).hom s = t := by
  have := subsingleton_subscheme_pointTestModule y hy
  exact exists_Γgerm_eq_pushforward_unit
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)) ^ 1).subschemeι
    (idealPowSubschemePoint (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))) one_ne_zero y
      (mem_support_vanishingIdeal_closure_singleton y)) t

/-- **The stalk of `𝒪_X/𝔪_y` at `y` is nonzero.** -/
theorem nontrivial_stalk_pointTestModule {X : Scheme.{u}} (y : X) :
    Nontrivial (ToType (TopCat.Presheaf.stalk (pointTestModule y 1).presheaf y)) :=
  Stacks.Chow.nontrivial_stalk_pushforwardStructureSheaf _
    (idealPowSubschemePoint (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))) one_ne_zero y
      (mem_support_vanishingIdeal_closure_singleton y))

/-! ### The two transports between the stalks at two equal points -/

/-- **A relation between germs of global sections transports along an equality of points.** -/
theorem Γgerm_smul_congr_point {X : Scheme.{u}} (F : X.Modules) {y x : X} (hyx : y = x)
    (V : X.Opens) (hyV : y ∈ V) (hxV : x ∈ V) (r : Γ(X, V)) (s s' : Γ(F, ⊤))
    (h : (F.presheaf.Γgerm y).hom s' =
      (X.presheaf.germ V y hyV) r • (F.presheaf.Γgerm y).hom s) :
    (F.presheaf.Γgerm x).hom s' =
      (X.presheaf.germ V x hxV) r • (F.presheaf.Γgerm x).hom s := by
  subst hyx
  exact h

/-- **Nonvanishing of the germ of a global section transports along an equality of points.** -/
theorem Γgerm_ne_zero_congr_point {X : Scheme.{u}} (F : X.Modules) {y x : X} (hyx : y = x)
    (s : Γ(F, ⊤)) (h : (F.presheaf.Γgerm y).hom s ≠ 0) :
    (F.presheaf.Γgerm x).hom s ≠ 0 := by
  subst hyx
  exact h

/-! ### Global sections as morphisms out of the structure sheaf -/

/-- **Every global section of a module is the value at `1` of a morphism out of `𝒪_X`.** -/
theorem exists_hom_unitModule_app_top_eq {X : Scheme.{u}} (F : X.Modules) (s : Γ(F, ⊤)) :
    ∃ t : Stacks.Ample.unitModule X ⟶ F,
      (t.app ⊤) (show Γ(Stacks.Ample.unitModule X, ⊤) from (1 : Γ(X, ⊤))) = s := by
  refine ⟨(Stacks.SectionRingGeometric.unitComparison X).inv ≫
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).symm s, ?_⟩
  have h := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply X F
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).symm s)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

/-! ### The stalk of `𝒪_X` is free of rank one on the germ of the unit section -/

/-- The germ at `x` of the unit section of `𝒪_X`, read in the stalk of `𝒪_X` as a module over
itself, in the `Stacks.ModuleSkyscraper.modulesStalkFunctor` spelling. -/
def unitΓgerm (X : Scheme.{u}) (x : X) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X) :=
  ((Stacks.Ample.unitModule X).presheaf.Γgerm x).hom
    (show Γ(Stacks.Ample.unitModule X, ⊤) from (1 : Γ(X, ⊤)))

/-- **`(𝒪_X)_x ≅ 𝒪_{X,x}`**, `Stacks.Ample.unitStalkEquiv` read in the
`Stacks.ModuleSkyscraper.modulesStalkFunctor` spelling of the stalk. -/
def unitStalkModuleEquiv (X : Scheme.{u}) (x : X) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X)
      ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  Stacks.Ample.unitStalkEquiv X x

/-- The comparison sends the germ of the unit section to `1`. -/
theorem unitStalkModuleEquiv_unitΓgerm (X : Scheme.{u}) (x : X) :
    unitStalkModuleEquiv X x (unitΓgerm X x) = 1 :=
  (Stacks.Ample.unitStalkFun_Γgerm X x _).trans (map_one (X.presheaf.Γgerm x).hom)

/-- The comparison sends `a` times the germ of the unit section to `a`. -/
private theorem unitStalkModuleEquiv_smul_unitΓgerm {X : Scheme.{u}} (x : X)
    (a : X.presheaf.stalk x) : unitStalkModuleEquiv X x (a • unitΓgerm X x) = a := by
  rw [map_smul, unitStalkModuleEquiv_unitΓgerm, smul_eq_mul, mul_one]

/-- Every element of the stalk of `𝒪_X` is a multiple of the germ of the unit section. -/
theorem exists_smul_unitΓgerm {X : Scheme.{u}} (x : X)
    (m : (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X)) :
    ∃ a : X.presheaf.stalk x, m = a • unitΓgerm X x :=
  ⟨unitStalkModuleEquiv X x m, (unitStalkModuleEquiv X x).injective
    (unitStalkModuleEquiv_smul_unitΓgerm x _).symm⟩

/-- The germ of the unit section is a free generator: only zero annihilates it. -/
theorem eq_zero_of_smul_unitΓgerm {X : Scheme.{u}} (x : X) {a : X.presheaf.stalk x}
    (h : a • unitΓgerm X x = 0) : a = 0 := by
  have h' := congrArg (unitStalkModuleEquiv X x) h
  rwa [unitStalkModuleEquiv_smul_unitΓgerm, map_zero] at h'

/-- `𝒪_X` is one of the coherent modules. -/
theorem coherentObjects_unitModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentObjects X (Stacks.Ample.unitModule X) :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X

/-- `𝒪_X/𝔪_y` is one of the coherent modules. -/
theorem coherentObjects_pointTestModule {X : Scheme.{u}} [IsLocallyNoetherian X] (y : X) :
    coherentObjects X (pointTestModule y 1) :=
  isCoherent_pointTestModule y 1

/-- **A cyclic module stays cyclic after extension of scalars**: if every element of `M` is a
multiple of `e`, then every element of `S ⊗_R M` is a scalar multiple of `1 ⊗ e`. -/
theorem exists_smul_unitApp_of_cyclic {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    {M : ModuleCat.{u} A} (e : M) (he : ∀ m : M, ∃ a : A, m = a • e)
    (u : (ModuleCat.extendScalars σ).obj M)
    (hu : u = ((ModuleCat.extendRestrictScalarsAdj σ).unit.app M) e)
    (ξ : (ModuleCat.extendScalars σ).obj M) : ∃ w : B, ξ = w • u := by
  let : Module A B := Module.compHom B σ
  have hsm : ∀ b : B, b • u = (b ⊗ₜ[A, σ] e : (ModuleCat.extendScalars σ).obj M) := by
    intro b
    subst hu
    have h := ModuleCat.ExtendScalars.smul_tmul σ (M := M) b 1 e
    rw [mul_one] at h
    exact h
  induction ξ using TensorProduct.inductionOn with
  | tmul b m =>
      obtain ⟨a, ha⟩ := he m
      subst ha
      exact ⟨a • (b : B), Eq.trans (TensorProduct.smul_tmul a b e).symm (hsm _).symm⟩
  | add p q hp hq =>
      obtain ⟨b, hb⟩ := hp
      obtain ⟨c, hc⟩ := hq
      exact ⟨b + c, by rw [hb, hc]; exact (add_smul b c u).symm⟩

/-- **The scalar of a comparison out of a cyclic base change is a unit.**  If `M` is generated
over `A` by `e` and `N` is free of rank one over `B` on `n`, then a `B`-linear isomorphism
`B ⊗_A M ≅ N` carries `1 ⊗ e` to `v · n` with `v` a unit. -/
theorem isUnit_of_extendScalars_iso {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (Λ : (ModuleCat.extendScalars σ).obj M ≅ N)
    (e : M) (he : ∀ m : M, ∃ a : A, m = a • e)
    (u : (ModuleCat.extendScalars σ).obj M)
    (hu : u = ((ModuleCat.extendRestrictScalarsAdj σ).unit.app M) e)
    (n : N) (hfree : ∀ b : B, b • n = 0 → b = 0)
    (v : B) (hv : (Λ.hom u : N) = v • n) :
    IsUnit v := by
  obtain ⟨ξ, hξ⟩ := (ConcreteCategory.bijective_of_isIso Λ.hom).2 n
  obtain ⟨w, hw⟩ := exists_smul_unitApp_of_cyclic σ e he u hu ξ
  have hms : (Λ.hom (w • u) : N) = w • (Λ.hom u : N) := map_smul _ _ _
  have hmul : (w * v) • n = n := by
    rw [mul_smul, ← hv, ← hms, ← hw, hξ]
  have hz := sub_eq_zero.1 (hfree (w * v - 1) (by rw [sub_smul, hmul, one_smul, sub_self]))
  exact ⟨⟨v, w, by rwa [mul_comm], hz⟩, rfl⟩

/-- For a semilinear `κ : M ⟶ N` sending `m` to `v · n` and `m'` to `v · n'`, with `m' = c · m` and
`n' = d · n`, the scalars satisfy `σ(c)·v = v·d` on `n`. -/
theorem smul_eq_of_semilinear {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (κ : M ⟶ (ModuleCat.restrictScalars σ).obj N) (v d : B) (c : A)
    (m m' : M) (n n' : N)
    (h1 : (κ m : N) = v • n) (h2 : (κ m' : N) = v • n')
    (hm : m' = c • m) (hn : n' = d • n) :
    (σ c * v) • n = (v * d) • n := by
  have e1 : (κ m' : N) = (σ c * v) • n := by
    rw [hm, map_smul, h1, mul_smul]
    rfl
  have e2 : (κ m' : N) = (v * d) • n := by rw [h2, hn, mul_smul]
  rw [← e1, e2]

/-- In a local ring `B`, a unit `v`, two elements `cs` and `d`, and a nonzero element `n` of a
`B`-module with `(cs·v)·n = (v·d)·n`, force `cs` and `d` to have the same residue. -/
theorem residue_eq_of_smul_eq {B : Type u} [CommRing B] [IsLocalRing B]
    {N : Type u} [AddCommGroup N] [Module B N] {v cs d : B} (hv : IsUnit v)
    {n : N} (hn : n ≠ 0) (h : (cs * v) • n = (v * d) • n) :
    IsLocalRing.residue B cs = IsLocalRing.residue B d := by
  have hann : (v * (cs - d)) • n = 0 := by
    rw [show v * (cs - d) = cs * v - v * d by ring, sub_smul, h, sub_self]
  exact Ideal.Quotient.eq.2 ((IsLocalRing.mem_maximalIdeal _).2 fun hu ↦
    hn ((hv.mul hu).smul_eq_zero.1 hann))

/-! ### The comparison `Λ`, the map `κ`, and their naturality -/

section NatIso

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (g : X ⟶ X)
  (θ : (coherentObjects X).ι ⋙ Scheme.Modules.pullback g ≅ (coherentObjects X).ι) (x : X)

/-- **`Λ_ℱ : 𝒪_{X,x} ⊗_{𝒪_{X,g x}} ℱ_{g x} ≅ ℱ_x`**, for a coherent `ℱ`: [Stacks, Tag 0098] in
the form `Stacks.ModuleSkyscraper.pullbackStalkIso`, composed with the stalk at `x` of the given
natural isomorphism `g^*ℱ ≅ ℱ`. -/
def lambdaIso (F : X.Modules) (hF : coherentObjects X F) :
    (ModuleCat.extendScalars (g.stalkMap x).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F) ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F :=
  (Stacks.ModuleSkyscraper.pullbackStalkIso g x).app F ≪≫
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapIso (θ.app ⟨F, hF⟩)

omit [IsLocallyNoetherian X] in
/-- The forward map of `lambdaIso` is the component at `F` of `pullbackStalkIso g x` followed by
the stalk at `x` of the component of `θ` at `F`. -/
theorem lambdaIso_hom (F : X.Modules) (hF : coherentObjects X F) :
    (lambdaIso g θ x F hF).hom =
      (Stacks.ModuleSkyscraper.pullbackStalkIso g x).hom.app F ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map (θ.hom.app ⟨F, hF⟩) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- **`Λ` is natural in `ℱ`.** -/
theorem lambdaIso_naturality {G F : X.Modules} (hG : coherentObjects X G)
    (hF : coherentObjects X F) (t : G ⟶ F) :
    (ModuleCat.extendScalars (g.stalkMap x).hom).map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).map t) ≫
        (lambdaIso g θ x F hF).hom =
      (lambdaIso g θ x G hG).hom ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map t := by
  have h1 : (ModuleCat.extendScalars (g.stalkMap x).hom).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).map t) ≫
        (Stacks.ModuleSkyscraper.pullbackStalkIso g x).hom.app F =
      (Stacks.ModuleSkyscraper.pullbackStalkIso g x).hom.app G ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map
          ((Scheme.Modules.pullback g).map t) :=
    (Stacks.ModuleSkyscraper.pullbackStalkIso g x).hom.naturality t
  have h2 : (Scheme.Modules.pullback g).map t ≫ θ.hom.app ⟨F, hF⟩ =
      θ.hom.app ⟨G, hG⟩ ≫ t :=
    θ.hom.naturality (ObjectProperty.homMk (X := (⟨G, hG⟩ : (coherentObjects X).FullSubcategory))
      (Y := ⟨F, hF⟩) t)
  rw [lambdaIso_hom, lambdaIso_hom, ← Category.assoc, h1, Category.assoc, ← Functor.map_comp,
    h2, Functor.map_comp, Category.assoc]

/-- **`κ_ℱ : ℱ_{g x} ⟶ ℱ_x`**, the `𝒪_{X,g x}`-linear map `m ↦ Λ_ℱ(1 ⊗ m)`. -/
def kappaHom (F : X.Modules) (hF : coherentObjects X F) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F ⟶
      (ModuleCat.restrictScalars (g.stalkMap x).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
  (ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.app
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F) ≫
    (ModuleCat.restrictScalars (g.stalkMap x).hom).map (lambdaIso g θ x F hF).hom

omit [IsLocallyNoetherian X] in
/-- `κ_ℱ(m) = Λ_ℱ(1 ⊗ m)`: the value of `kappaHom` at `m` is `lambdaIso` applied to the image of
`m` under the unit of the extension–restriction of scalars adjunction. -/
theorem kappaHom_eq_lambda_unitApp (F : X.Modules) (hF : coherentObjects X F)
    (m : (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F) :
    (kappaHom g θ x F hF m :
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) =
      (lambdaIso g θ x F hF).hom
        (((ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F)) m) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- **`κ` is natural.** -/
theorem kappaHom_naturality {G F : X.Modules} (hG : coherentObjects X G)
    (hF : coherentObjects X F) (t : G ⟶ F) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).map t ≫ kappaHom g θ x F hF =
      kappaHom g θ x G hG ≫ (ModuleCat.restrictScalars (g.stalkMap x).hom).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map t) := by
  have hu : (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).map t ≫
        (ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj F) =
      (ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj G) ≫
        (ModuleCat.restrictScalars (g.stalkMap x).hom).map
          ((ModuleCat.extendScalars (g.stalkMap x).hom).map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).map t)) :=
    (ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.naturality _
  rw [kappaHom, kappaHom, ← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    lambdaIso_naturality g θ x hG hF t, Functor.map_comp, ← Category.assoc]

/-- The scalar of `𝒪_{X,x}` by which the natural isomorphism acts on the germs of global
sections. -/
def natIsoUnitScalar : X.presheaf.stalk x :=
  unitStalkModuleEquiv X x
    ((kappaHom g θ x (Stacks.Ample.unitModule X) (coherentObjects_unitModule X)
        (unitΓgerm X (g.base x)) :
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X)))

/-- `κ_{𝒪_X}` carries the germ at `g x` of the unit section to `natIsoUnitScalar g θ x` times the
germ at `x` of the unit section. -/
theorem kappaHom_unitΓgerm :
    (kappaHom g θ x (Stacks.Ample.unitModule X) (coherentObjects_unitModule X)
        (unitΓgerm X (g.base x)) :
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X)) =
      natIsoUnitScalar g θ x • unitΓgerm X x := by
  refine (unitStalkModuleEquiv X x).injective ?_
  rw [unitStalkModuleEquiv_smul_unitΓgerm]
  rfl

/-- **The scalar `natIsoUnitScalar g θ x` is a unit.** -/
theorem isUnit_natIsoUnitScalar : IsUnit (natIsoUnitScalar g θ x) :=
  isUnit_of_extendScalars_iso (g.stalkMap x).hom
    (lambdaIso g θ x (Stacks.Ample.unitModule X) (coherentObjects_unitModule X))
    (unitΓgerm X (g.base x)) (exists_smul_unitΓgerm (g.base x))
    (((ModuleCat.extendRestrictScalarsAdj (g.stalkMap x).hom).unit.app
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g.base x)).obj
        (Stacks.Ample.unitModule X))) (unitΓgerm X (g.base x))) rfl
    (unitΓgerm X x) (fun _ hb ↦ eq_zero_of_smul_unitΓgerm x hb)
    (natIsoUnitScalar g θ x)
    ((kappaHom_eq_lambda_unitApp g θ x (Stacks.Ample.unitModule X)
      (coherentObjects_unitModule X) (unitΓgerm X (g.base x))).symm.trans
      (kappaHom_unitΓgerm g θ x))

/-! ### `κ` on the germs of global sections -/

/-- **`κ_ℱ` on the germ of a global section**: `κ_ℱ` carries the germ at `g x` of a global
section `s` to `natIsoUnitScalar g θ x` times the germ of `s` at `x`. -/
theorem kappaHom_Γgerm (F : X.Modules) (hF : coherentObjects X F) (s : Γ(F, ⊤)) :
    (kappaHom g θ x F hF ((F.presheaf.Γgerm (g.base x)).hom s) :
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) =
      natIsoUnitScalar g θ x • ((F.presheaf.Γgerm x).hom s) := by
  obtain ⟨t, ht⟩ := exists_hom_unitModule_app_top_eq F s
  have hnat := kappaHom_naturality g θ x (coherentObjects_unitModule X) hF t
  have hmap : ∀ y : X, (Stacks.ModuleSkyscraper.modulesStalkFunctor X y).map t (unitΓgerm X y) =
      (F.presheaf.Γgerm y).hom s := fun y ↦ by
    rw [unitΓgerm, ← ht]
    exact Stacks.ModuleSkyscraper.modulesStalkFunctor_map_germ y t ⊤ trivial _
  have hev := congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) (unitΓgerm X (g.base x))) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hev
  rw [hmap] at hev
  rw [hev]
  change (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map t
      ((kappaHom g θ x (Stacks.Ample.unitModule X) (coherentObjects_unitModule X)
        (unitΓgerm X (g.base x)) :
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (Stacks.Ample.unitModule X))) = _
  rw [kappaHom_unitΓgerm g θ x, map_smul, hmap]
  rfl

/-! ### The comorphism induces the identity on the residue field -/

include θ in
/-- For a closed point `x` fixed by `g`, the comorphism `g^♯_x` and the germ at `x` of a section
over a neighbourhood agree modulo `𝔪_x`. -/
theorem residue_stalkMap_germ_eq_of_natIso
    (hx : IsClosed ({x} : Set X)) (hgx : g.base x = x)
    (V : X.Opens) (hyV : g.base x ∈ V) (hxV : x ∈ V) (r : Γ(X, V)) :
    (X.residue x) ((g.stalkMap x) ((X.presheaf.germ V (g.base x) hyV) r)) =
      (X.residue x) ((X.presheaf.germ V x hxV) r) := by
  have hy : IsClosed ({g.base x} : Set X) := by rwa [hgx]
  have := nontrivial_stalk_pointTestModule (X := X) (g.base x)
  have hF : coherentObjects X (pointTestModule (g.base x) 1) :=
    coherentObjects_pointTestModule (g.base x)
  obtain ⟨n, hn⟩ := exists_ne
    (0 : ToType (TopCat.Presheaf.stalk (pointTestModule (g.base x) 1).presheaf (g.base x)))
  obtain ⟨s, hs⟩ := exists_Γgerm_eq_pointTestModule (g.base x) hy n
  have hsne : ((pointTestModule (g.base x) 1).presheaf.Γgerm x).hom s ≠ 0 :=
    Γgerm_ne_zero_congr_point _ hgx s (by rwa [hs])
  obtain ⟨s', hs'⟩ := exists_Γgerm_eq_pointTestModule (g.base x) hy
    ((X.presheaf.germ V (g.base x) hyV) r •
      ((pointTestModule (g.base x) 1).presheaf.Γgerm (g.base x)).hom s)
  have htr : ((pointTestModule (g.base x) 1).presheaf.Γgerm x).hom s' =
      (X.presheaf.germ V x hxV) r •
        ((pointTestModule (g.base x) 1).presheaf.Γgerm x).hom s :=
    Γgerm_smul_congr_point _ hgx V hyV hxV r s s' hs'
  exact residue_eq_of_smul_eq (isUnit_natIsoUnitScalar g θ x) hsne
    (smul_eq_of_semilinear (g.stalkMap x).hom
      (kappaHom g θ x (pointTestModule (g.base x) 1) hF)
      (natIsoUnitScalar g θ x) ((X.presheaf.germ V x hxV) r)
      ((X.presheaf.germ V (g.base x) hyV) r) _ _ _ _
      (kappaHom_Γgerm g θ x _ hF s) (kappaHom_Γgerm g θ x _ hF s') hs' htr)

include θ in
/-- **The morphism `Spec κ(x) ⟶ X` of a fixed closed point is unchanged by `g`.** -/
theorem fromSpecResidueField_comp_eq_of_natIso
    (hx : IsClosed ({x} : Set X)) (hgx : g.base x = x) :
    X.fromSpecResidueField x ≫ g = X.fromSpecResidueField x := by
  refine fromSpecResidueField_comp_eq_of_stalkMap_residue g x hgx ?_
  rw [X.residue_residueFieldCongr hgx]
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  obtain ⟨V, hyV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have hxV : x ∈ V := hgx ▸ hyV
  have h1 : (X.presheaf.stalkCongr (Inseparable.of_eq hgx)).hom a =
      (X.presheaf.germ V x hxV) r := by
    rw [← hr]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hyV
      (Inseparable.of_eq hgx).ge r
  change (X.residue x) ((g.stalkMap x) a) = (X.residue x)
    ((X.presheaf.stalkCongr (Inseparable.of_eq hgx)).hom a)
  rw [h1, ← hr]
  exact residue_stalkMap_germ_eq_of_natIso g θ x hx hgx V hyV hxV r

end NatIso

/-! ### Sections of the second projection representing the identity -/

section Kernel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- Let `X` be smooth and proper over a field `k`, let `K` be an object of `D(𝒪_{X ×_k X})` whose
Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity, and let
`s : X ⟶ X ×_k X` be a section of the second projection with `K ≅ Rs_*𝒪_X`. Then `pr_1 ∘ s = 𝟙 X`.
-/
theorem comp_fst_eq_id_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (eK : K ≅ (dpush s).obj (derivedUnitObject X)) :
    s ≫ Limits.pullback.fst f f = 𝟙 X := by
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  refine AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField f s hsnd
    fun x hx ↦ ?_
  refine (nonempty_natIso_pullback_coherentObjects_of_representsIdentityOnPerfect
    f K hΦ s hsnd eK).elim fun θ ↦ ?_
  exact fromSpecResidueField_comp_eq_of_natIso (s ≫ Limits.pullback.fst f f) θ x
    (mem_closedPoints_iff.1 hx)
    (AlgebraicGeometry.base_comp_fst_eq_self_of_representsIdentityOnPerfect f K hΦ s hsnd eK x)

/-- Let `X` be smooth and proper over a field `k` and let `K` be an object of `D(𝒪_{X ×_k X})`
whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity. If
`K ≅ Rs_*𝒪_X` for a section `s` of the second projection, then `K` is isomorphic to the diagonal
kernel `diagonalFourierMukaiKernel f`. -/
theorem iso_diagonalFourierMukaiKernel_of_exists_section
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (hsection : ∃ s : X ⟶ Limits.pullback f f, s ≫ Limits.pullback.snd f f = 𝟙 X ∧
      Nonempty (K ≅ (dpush s).obj (derivedUnitObject X))) :
    Nonempty (K ≅ diagonalFourierMukaiKernel f) := by
  obtain ⟨s, hsnd, ⟨eK⟩⟩ := hsection
  exact iso_diagonalFourierMukaiKernel_of_isSection f K s
    (comp_fst_eq_id_of_representsIdentityOnPerfect f K hΦ s hsnd eK) hsnd eK

end Kernel

end Stacks.Duality

end
