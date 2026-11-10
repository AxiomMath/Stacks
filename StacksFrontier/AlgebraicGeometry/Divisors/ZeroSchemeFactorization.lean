module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Factorization through the zero scheme of a section

A morphism of schemes `f : Y ⟶ X` factors through the zero scheme of a global section `s` of an
invertible `𝒪_X`-module `L` exactly when the pulled-back section `f^*s` vanishes. This is
[Stacks, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR) (2), and (1) follows from it.

## Main results

* `AlgebraicGeometry.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme`: **Tag 02OR (2)**.
* `AlgebraicGeometry.zeroScheme_isGreatest_vanishingClosedSubscheme`: **Tag 02OR (1)**, the
  zero scheme is the largest closed subscheme on which the section pulls back to zero.

## Implementation notes

Factoring through a closed subscheme is an inequality of ideal sheaves,
`factorsThrough_ideal_iff_ideal_le_ker`, so the whole statement is local on `X` and on `Y`. The
local comparison is made on a pair of affine opens `V ⊆ f⁻¹U` with `L` trivialized on `U`: there
the base-change comparison `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
identifies `Γ(f^*L, V)` with `Γ(Y, V) ⊗_{Γ(X, U)} Γ(L, U)`, the trivialization identifies the
second factor with `Γ(X, U)`, and the pulled-back section becomes the image of the single
function `a` that represents `s` on `U` — which is exactly the generator of the ideal of the
zero scheme there (`zeroScheme_ideal_of_trivialization`).

So no sheaf-level trivialization of `L` and no manipulation of the pullback-pushforward
adjunction beyond the existing `Scheme.Modules.pullbackSection` API is needed; the two gluing
steps are both ordinary applications of the sheaf condition on `Y`.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- Factoring a morphism through the closed subscheme cut out by an ideal sheaf is the same as
that ideal sheaf being below the kernel of the morphism. -/
theorem factorsThrough_ideal_iff_ideal_le_ker {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ I.subscheme, g ≫ I.subschemeι = f) ↔ I ≤ f.ker := by
  constructor
  · rintro ⟨g, hg⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι I, ← hg]
    exact Scheme.Hom.le_ker_comp g I.subschemeι
  · intro h
    exact ⟨f.toImage ≫ Scheme.IdealSheafData.inclusion h, by simp⟩

/-- The canonical map on global sections is the pullback of the global section. -/
theorem pullbackGlobalSections_eq_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens)) (s : Γ(L, ⊤)) :
    pullbackGlobalSections f L s = Scheme.Modules.pullbackSection f L ⊤ ⊤ h s := rfl

/-- Two successive restrictions of a section of a module are the composite restriction. -/
private theorem presheaf_map_homOfLE_apply {Y : Scheme.{u}} (M : Y.Modules)
    {V₁ V₂ V₃ : Y.Opens} (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (h₃ : V₁ ≤ V₃) (t : M.presheaf.obj (op V₃)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op t) =
      M.presheaf.map (homOfLE h₃).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Pulling back a section and then restricting is the same as restricting the section to a
smaller open of the target first. -/
theorem pullbackSection_res_source {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    {U U' : X.Opens} (hUU' : U' ≤ U) {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ f ⁻¹ᵁ U')
    (a : Γ(L, U)) :
    Scheme.Modules.pullbackSection f L U' V h' (L.presheaf.map (homOfLE hUU').op a) =
      Scheme.Modules.pullbackSection f L U V h a := by
  have hpre : f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U := fun z hz => hUU' hz
  set t := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) a
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U')
        (L.presheaf.map (homOfLE hUU').op a) =
      ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE hpre).op t :=
    PresheafOfModules.naturality_apply _ _ _
  unfold Scheme.Modules.pullbackSection
  rw [hnat]
  exact presheaf_map_homOfLE_apply _ h' hpre h t

/-- Under an identification of a module with the ring, `1 ⊗ b` vanishes in a base change
exactly when the function representing `b` does. The scalar action on the target is a
*parameter*, so this is applied to the action the extension of scalars uses and nothing is
re-elaborated. -/
private theorem tmul_one_eq_zero_iff {R S M : Type u} [CommRing R] [CommRing S] [Module R S]
    [AddCommGroup M] [Module R M] (φ : R →+* S)
    (hsmul : ∀ (r : R) (t : S), r • t = φ r * t) (e : M ≃ₗ[R] R) (b : M) :
    (1 : S) ⊗ₜ[R] b = 0 ↔ φ (e b) = 0 := by
  have key : ((TensorProduct.congr (LinearEquiv.refl R S) e).trans
      (TensorProduct.rid R S)) ((1 : S) ⊗ₜ[R] b) = φ (e b) := by
    simp [hsmul]
  rw [← key, LinearEquiv.map_eq_zero_iff]

/-- **The affine-local vanishing criterion**, with the base-change comparison as a parameter so
that the two spellings of `1 ⊗ b` never have to be reconciled under a named definition. -/
private theorem pullbackSection_eq_zero_iff_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) {U : X.Opens} {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (Φ : ((ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(L, U))) ≅
      ModuleCat.of Γ(Y, V) Γ((Scheme.Modules.pullback f).obj L, V))
    (hΦ : ∀ b : Γ(L, U), Φ.hom ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] b) =
      Scheme.Modules.pullbackSection f L U V hVU b)
    (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (b : Γ(L, U)) :
    Scheme.Modules.pullbackSection f L U V hVU b = 0 ↔ f.appLE U V hVU (e b) = 0 := by
  have h1 : Scheme.Modules.pullbackSection f L U V hVU b = 0 ↔
      ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] b) = 0 := by
    rw [← hΦ b]
    exact map_eq_zero_iff (ConcreteCategory.hom Φ.hom)
      (ConcreteCategory.bijective_of_isIso Φ.hom).injective
  exact h1.trans (@tmul_one_eq_zero_iff Γ(X, U) Γ(Y, V) Γ(L, U) _ _
    (Module.compHom _ (f.appLE U V hVU).hom) _ _ (f.appLE U V hVU).hom
    (fun _ _ => rfl) e b)

/-- **The affine-local vanishing criterion.** On a pair of affine opens `V ⊆ f⁻¹U` with the
invertible module trivialized on `U` by `e`, the pullback of a section of `L` over `U` vanishes
on `V` exactly when the function representing it does. -/
theorem pullbackSection_eq_zero_iff_appLE_eq_zero {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) [L.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U))
    (b : Γ(L, U)) :
    Scheme.Modules.pullbackSection f L U V hVU b = 0 ↔ f.appLE U V hVU (e b) = 0 :=
  pullbackSection_eq_zero_iff_of_iso f L hVU
    (affinePullbackSectionsBaseChangeIso f L hU hV hVU)
    (affinePullbackSectionsBaseChangeIso_one_tmul f L hU hV hVU) e b

/-- Restricting the pullback of a section to a smaller open of the source. -/
theorem pullbackSection_res_target {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    {U : X.Opens} {V V' : Y.Opens} (hV'V : V' ≤ V) (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U)
    (a : Γ(L, U)) :
    ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE hV'V).op
        (Scheme.Modules.pullbackSection f L U V h a) =
      Scheme.Modules.pullbackSection f L U V' h' a := by
  set t := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) a
  unfold Scheme.Modules.pullbackSection
  exact presheaf_map_homOfLE_apply _ hV'V h h' t

/-- If the pullback of a global section vanishes, so does its pullback read over any open of
the target restricted to any open of the source. -/
theorem pullbackSection_eq_zero_of_pullbackGlobalSections_eq_zero {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (s : Γ(L, ⊤)) (h0 : pullbackGlobalSections f L s = 0) {U : X.Opens}
    {V : Y.Opens} (hV : V ≤ f ⁻¹ᵁ U) :
    Scheme.Modules.pullbackSection f L U V hV
      (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = 0 := by
  have htop : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens) := by simp
  have hVtop : V ≤ f ⁻¹ᵁ (⊤ : X.Opens) := by simp
  rw [pullbackSection_res_source f L (le_top : U ≤ ⊤) hVtop hV s,
    ← pullbackSection_res_target f L (le_top : V ≤ ⊤) htop hVtop s,
    ← pullbackGlobalSections_eq_pullbackSection f L htop s, h0, map_zero]
  rfl

/-- The pullback of a global section vanishes on `V` exactly when it does so for the function
representing the section on a trivializing affine open above `V`. -/
theorem pullbackSection_eq_zero_iff_appLE_eq_zero_of_trivialization {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : X.Modules) [L.IsQuasicoherent] (s : Γ(L, ⊤)) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    Scheme.Modules.pullbackSection f L U V hVU
        (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = 0 ↔
      f.appLE U V hVU (e (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)) = 0 :=
  pullbackSection_eq_zero_iff_appLE_eq_zero f L hU hV hVU e _

/-- Being below the kernel ideal sheaf is checked on affine opens. -/
private theorem le_ker_iff {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    I ≤ f.ker ↔ ∀ U : X.affineOpens, I.ideal U ≤ RingHom.ker (f.app U.1).hom :=
  Scheme.IdealSheafData.le_ofIdeals_iff

/-- The data the local argument needs above a point of an affine open: a trivializing basic
open of that affine open, and an affine open of the source mapping into it. -/
private theorem exists_trivializing_pair {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (U : X.affineOpens) (y : Y) (hy : f y ∈ U.1) :
    ∃ (g : Γ(X, U.1)) (V : Y.Opens), IsAffineOpen V ∧ y ∈ V ∧ V ≤ f ⁻¹ᵁ X.basicOpen g ∧
      X.basicOpen g ≤ U.1 ∧
      Nonempty (Γ(L, X.basicOpen g) ≃ₗ[Γ(X, X.basicOpen g)] Γ(X, X.basicOpen g)) := by
  obtain ⟨g, hfy, hgU, he⟩ := exists_basicOpen_linearEquiv L U (f y) hy
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hyV, hVsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ X.basicOpen g from hfy) (f ⁻¹ᵁ X.basicOpen g).isOpen
  exact ⟨g, V, hVaff, hyV, hVsub, hgU, he⟩

/-- The same data above an arbitrary point of the source. -/
private theorem exists_trivializing_pair_top {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (y : Y) :
    ∃ (W : X.Opens) (V : Y.Opens), IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ V ≤ f ⁻¹ᵁ W ∧
      Nonempty (Γ(L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) := by
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem (f y)
  obtain ⟨g, V, hVaff, hyV, hVsub, -, he⟩ := exists_trivializing_pair f L U y hU
  exact ⟨X.basicOpen g, V, U.2.basicOpen g, hVaff, hyV, hVsub, he⟩

/-- Restriction of a section of the structure sheaf along `f`, as an `appLE`. -/
private theorem map_app_eq_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (hV : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)) :
    Y.presheaf.map (homOfLE hV).op (f.app U x) = f.appLE U V hV x :=
  (ConcreteCategory.comp_apply (f.app U) (Y.presheaf.map (homOfLE hV).op) x).symm

/-- **Stacks Tag 02OR (2).** A global section of an invertible module vanishes after pullback
along `f` if and only if `f` factors through its zero scheme. -/
@[stacks 02OR "factorization"]
theorem pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackGlobalSections f L s = 0 ↔
      ∃ g : Y ⟶ (zeroScheme X L s).subscheme,
        g ≫ (zeroScheme X L s).subschemeι = f := by
  have hqc := isQuasicoherent_of_isInvertible L
  have htop : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens) := by simp
  rw [factorsThrough_ideal_iff_ideal_le_ker, le_ker_iff]
  constructor
  · intro h0 U x hx
    rw [RingHom.mem_ker]
    choose gg VV hVaff hyV hVsub hgU he using
      fun y : (f ⁻¹ᵁ U.1 : Y.Opens) => exists_trivializing_pair f L U y.1 y.2
    have hVU : ∀ y, VV y ≤ f ⁻¹ᵁ U.1 := fun y z hz => hgU y (hVsub y hz)
    have hcover : (f ⁻¹ᵁ U.1 : Y.Opens) ≤ ⨆ y, VV y := fun z hz =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyV ⟨z, hz⟩⟩
    refine Y.sheaf.eq_of_locally_eq' (U := VV) (f ⁻¹ᵁ U.1)
      (fun y => homOfLE (hVU y)) hcover _ 0 fun y => ?_
    refine Eq.trans ?_ (map_zero _).symm
    refine (map_app_eq_appLE f (hVU y) x).trans ?_
    rw [← Scheme.Hom.map_appLE f (hVsub y) (homOfLE (hgU y)).op,
      ConcreteCategory.comp_apply]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
      (((zeroScheme_ideal_of_trivialization X L s ⟨X.basicOpen (gg y), U.2.basicOpen (gg y)⟩
          (he y).some _ rfl) ▸
        (zeroScheme X L s).ideal_le_comap_ideal (hgU y) hx :
          X.presheaf.map (homOfLE (hgU y)).op x ∈
            Ideal.span {(he y).some (L.presheaf.map (homOfLE le_top).op s)}))
    rw [← hc, map_mul,
      (pullbackSection_eq_zero_iff_appLE_eq_zero_of_trivialization f L s
        (U.2.basicOpen (gg y)) (hVaff y) (hVsub y) (he y).some).mp
        (pullbackSection_eq_zero_of_pullbackGlobalSections_eq_zero f L s h0 (hVsub y)),
      mul_zero]
    rfl
  · intro hle
    choose WW VV hWaff hVaff hyV hVsub hee using
      fun y : Y => exists_trivializing_pair_top f L y
    have hcover : (⊤ : Y.Opens) ≤ ⨆ y, VV y := fun z _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hyV z⟩
    let F : TopCat.Sheaf AddCommGrpCat Y :=
      ⟨((Scheme.Modules.pullback f).obj L).presheaf,
        ((Scheme.Modules.pullback f).obj L).isSheaf⟩
    refine F.eq_of_locally_eq' (U := VV) ⊤ (fun y => homOfLE le_top) hcover _ 0 fun y => ?_
    have hVtop : VV y ≤ f ⁻¹ᵁ (⊤ : X.Opens) := by simp
    simp only [map_zero]
    change ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE (le_top : VV y ≤ ⊤)).op
      (pullbackGlobalSections f L s) = 0
    rw [pullbackGlobalSections_eq_pullbackSection f L htop s,
      pullbackSection_res_target f L (le_top : VV y ≤ ⊤) htop hVtop s,
      ← pullbackSection_res_source f L (le_top : WW y ≤ ⊤) hVtop (hVsub y) s]
    refine (pullbackSection_eq_zero_iff_appLE_eq_zero_of_trivialization f L s
      (hWaff y) (hVaff y) (hVsub y) (hee y).some).mpr ?_
    rw [← map_app_eq_appLE f (hVsub y)]
    have hmem : (hee y).some (L.presheaf.map (homOfLE (le_top : WW y ≤ ⊤)).op s) ∈
        (zeroScheme X L s).ideal ⟨WW y, hWaff y⟩ := by
      rw [zeroScheme_ideal_of_trivialization X L s ⟨WW y, hWaff y⟩ (hee y).some _ rfl]
      exact Ideal.subset_span rfl
    rw [RingHom.mem_ker.mp (hle ⟨WW y, hWaff y⟩ hmem), map_zero]

/-- **Stacks Tag 02OR (1).** Among the closed subschemes on which the section pulls back to
zero, the zero scheme is the largest. Closed subschemes are ordered by their ideal sheaves, and
geometric inclusion is the reverse of that order, which is why the statement is about the order
dual. -/
@[stacks 02OR "maximal"]
theorem zeroScheme_isGreatest_vanishingClosedSubscheme (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤)) :
    IsGreatest
      {I : (X.IdealSheafData)ᵒᵈ |
        pullbackGlobalSections (OrderDual.ofDual I).subschemeι L s = 0}
      (OrderDual.toDual (zeroScheme X L s)) := by
  refine ⟨(pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s
    (zeroScheme X L s).subschemeι).2 ⟨𝟙 _, Category.id_comp _⟩, ?_⟩
  intro I hI
  change zeroScheme X L s ≤ OrderDual.ofDual I
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using
    (factorsThrough_ideal_iff_ideal_le_ker _ _).1
      ((pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s
        (OrderDual.ofDual I).subschemeι).1 hI)

end AlgebraicGeometry

end
