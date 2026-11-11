module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SheafExtLocalVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ClosedSubsetCodimensionBound
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SupportedSheafCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SeparatedCohomologyHomVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SeparatedCohomologyHomVanishingPredicate
public import StacksCore.Tactic.StacksAttribute

/-!
# Ext vanishing above the dimension on a regular Noetherian scheme

Let `X` be a regular Noetherian scheme of finite dimension `d`. For a coherent `𝒪_X`-module `F`
and an arbitrary `𝒪_X`-module `G`, `Ext^n_X(F, G) = 0` for every `n > d`. In the form of
`Abelian.zExt` this is part (1) of [Stacks, Tag 0FZ3]. Fed into the vanishing of morphisms
between complexes with separated cohomological ranges of
`StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SeparatedCohomologyHomVanishing`, it gives
part (2).

## The argument

Choose an injective resolution `G ⟶ I^•`. Morphisms `F ⟶ I^n` are the global sections of the
internal Hom `𝓗om(F, I^n)`, so `Ext^n(F, G)` is the `n`-th cohomology of the complex of global
sections of `C^• = 𝓗om(F, I^•)`. Each `C^q` is flasque, hence acyclic, and the cohomology sheaves
of `C^•` are the sheaf Ext's `𝓔xt^q(F, G)`. At a point `y` with `d_y = dim 𝒪_{X,y}`, the local ring
is regular, so the stalk `F_y` has projective dimension at most `d_y` ([Stacks, Tag 00O7]), and
`𝓔xt^q(F, G)` vanishes on a neighbourhood of `y` for `q > d_y`
(`Stacks.SheafHomInjective.exists_vanishesOn_homology_of_hasProjectiveDimensionLT`). Hence
`𝓔xt^q(F, G)` is supported on a closed subset all of whose points have local rings of dimension
at least `q`, which has dimension at most `d - q`
(`AlgebraicGeometry.topologicalKrullDim_le_sub_of_le_ringKrullDim_stalk`), so
`H^p(X, 𝓔xt^q(F, G)) = 0` for `p > d - q` ([Stacks, Tag 02UZ], in the supported form
`Stacks.SupportedVanishing.subsingleton_ext_of_isZero_stalk`). These are the inputs of the
hypercohomology bound `Stacks.ExtCycles.exists_comp_d_eq_of_subsingleton_ext_homology`, which
gives the vanishing of the cohomology of the global sections of `C^•` above `d`; this is the
vanishing of `Ext^n(F, G)` by `Stacks.ExtCycles.subsingleton_ext_iff_forall_cycle_boundary`.
This is the local-to-global spectral sequence of [Stacks, Tag 0BQP], used only through the
vanishing it implies.

## Main results

* `AlgebraicGeometry.subsingleton_ext_of_isRegular`: `Ext^{m+1}(F, G) = 0` for `F` coherent,
  `G` arbitrary and `d < m + 1`.
* `AlgebraicGeometry.subsingleton_zExt_of_isRegular`: **[Stacks, Tag 0FZ3] part (1).**
* `AlgebraicGeometry.subsingleton_hom_of_homology_separated_of_isRegular`:
  **[Stacks, Tag 0FZ3] part (2).**
* `AlgebraicGeometry.forall_separatedCohomologyHomVanishing`: part (2) for every Noetherian
  scheme and every dimension, in the form of `AlgebraicGeometry.SeparatedCohomologyHomVanishing`.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
* [Stacks Project, Tag 00O7](https://stacks.math.columbia.edu/tag/00O7)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open Stacks.SheafHomInjective Stacks.SupportedVanishing

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The underlying abelian sheaf of a module vanishing near `x` has zero stalk at `x`. -/
theorem isZero_stalk_toSheaf_of_vanishesOn
    {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} {U : X.Opens}
    (h : VanishesOn E U) {x : X} (hx : x ∈ U) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj E).obj x) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
  suffices ∀ m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf x, m = 0 by
    rw [this a, this b]
  intro m
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf m
  rw [← TopCat.Presheaf.germ_res_apply E.val.presheaf (homOfLE (inf_le_left : V ⊓ U ≤ V)) x
    ⟨hxV, hx⟩ s, h (V ⊓ U) inf_le_right (E.val.presheaf.map (homOfLE inf_le_left).op s)]
  exact map_zero _

/-- An abelian sheaf all of whose stalks vanish is zero. -/
theorem isZero_of_isZero_stalk (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (h : ∀ x : X,
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) E.obj x)) :
    IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext V s
  change s = 0
  refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) (X := X.toTopCat) E V.unop s 0
    fun x hx => ?_
  have := AddCommGrpCat.isZero_iff_subsingleton.1 (h x)
  exact Subsingleton.elim _ _

/-- **The cohomology sheaves of `𝓗om(F, I^•)` are supported in small dimension.** On a regular
Noetherian scheme of dimension `d`, for `F` coherent, `G` arbitrary with injective resolution
`I^•`, and for every `q` and `k` with `d < k + q`, the sheaf `𝓔xt^q(F, G)` has
`H^k(X, 𝓔xt^q(F, G)) = 0`. -/
theorem subsingleton_ext_homology_cx_of_isRegular [IsNoetherian X] (hX : IsRegular X) (d : ℕ)
    (hd : topologicalKrullDim X = d)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (hF : SheafOfModules.IsCoherent F) (Res : InjectiveResolution G)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (q k : ℕ) (hqk : d < k + q) :
    Subsingleton (Ext.{u} (constZ X.toTopCat)
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj
        ((cx X.sheaf F Res.cocomplex).homology q)) k) := by
  have hreg := ((isRegular_tfae X).out 1 2).1 hX
  have : IsLocallyNoetherian X := hreg.1
  have hdy : ∀ y : X, ∃ n : ℕ, n ≤ d ∧ ringKrullDim (X.presheaf.stalk y) = n := by
    intro y
    have h₁ := coheight_le_topologicalKrullDim y
    rw [hd] at h₁
    have h₂ : Order.coheight y ≤ (d : ℕ∞) := by exact_mod_cast h₁
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top d) h₂)
    refine ⟨n, by exact_mod_cast hn ▸ h₂, ?_⟩
    rw [ringKrullDim_stalk_eq_coheight, ← hn]
    rfl
  choose dy hdy_le hdy_eq using hdy
  have : Stacks.SheafOfModules.IsCoherent F :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hF
  have hpd : ∀ y : X, HasProjectiveDimensionLT ((stk y).obj F) (dy y + 1) := fun y =>
    have := hreg.2 y
    hasProjectiveDimensionLE_stalk y (le_of_eq (hdy_eq y)) _
  choose U hyU hU using fun y : X =>
    exists_vanishesOn_homology_of_hasProjectiveDimensionLT Res y (dy y) F ⊤
      (Stacks.SheafOfModules.isCoherentOn_of_isCoherent F ⊤) trivial (hpd y)
  let W : X.Opens := ⨆ y : {y : X // dy y < q}, U y.1
  let Z : Set X := (W : Set X)ᶜ
  have hZc : IsClosed Z := W.isOpen.isClosed_compl
  let E := (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj
    ((cx X.sheaf F Res.cocomplex).homology q)
  have hvan : ∀ x : X, x ∉ Z →
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) E.obj x) := by
    intro x hx
    have hxW : x ∈ W := by simpa [Z] using hx
    obtain ⟨⟨y, hy⟩, hxy⟩ := (Opens.mem_iSup).1 hxW
    have h := hU y (q - dy y - 1)
    rw [show q - dy y - 1 + dy y + 1 = q by omega] at h
    exact isZero_stalk_toSheaf_of_vanishesOn h hxy
  have hZ : ∀ z ∈ Z, q ≤ dy z := by
    intro z hz
    by_contra hlt
    exact hz ((Opens.mem_iSup).2 ⟨⟨z, by omega⟩, hyU z⟩)
  by_cases hq : q ≤ d
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hdimZ : topologicalKrullDim Z ≤ ((d - q : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_le_sub_of_le_ringKrullDim_stalk hd hZc fun z hz => by
        rw [hdy_eq z]
        exact_mod_cast hZ z hz
    have : NoetherianSpace X.toTopCat := inferInstanceAs (NoetherianSpace X)
    exact subsingleton_ext_of_isZero_stalk (X := X.toTopCat) Z hZc hdimZ E hvan k' (by omega)
  · exact Stacks.ExtCycles.subsingleton_ext_of_isZero _
      (isZero_of_isZero_stalk E fun x => hvan x fun hx => hq ((hZ x hx).trans (hdy_le x))) k

/-- The section of `𝓗om(A, I)` given by the zero morphism is zero. -/
theorem sectionOf_zero {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (U : X.Opens) : sectionOf U (0 : A ⟶ I) = 0 :=
  PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **Ext vanishing above the dimension.** On a regular Noetherian scheme of dimension `d`,
`Ext^{m+1}(F, G) = 0` for `F` coherent, `G` arbitrary and `d < m + 1`. -/
theorem subsingleton_ext_of_isRegular [IsNoetherian X] (hX : IsRegular X) (d : ℕ)
    (hd : topologicalKrullDim X = d)
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (hF : SheafOfModules.IsCoherent F)
    [HasExt.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))]
    (m : ℕ) (hm : d < m + 1) :
    Subsingleton (Ext.{u} F G (m + 1)) := by
  have : EnoughInjectives
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    IsGrothendieckAbelian.enoughInjectives
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt _
  let Res := injectiveResolution G
  let T := SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
  let K := cx X.sheaf F Res.cocomplex
  let C := (T.mapHomologicalComplex _).obj K
  refine (Stacks.ExtCycles.subsingleton_ext_iff_forall_cycle_boundary_of_isLimit F Res.cocomplex
    (hw := Res.ι_f_zero_comp_complex_d)
    Res.isLimitKernelFork Res.cocomplex_exactAt_succ
    (fun q k => ⟨fun a b => (Ext.eq_zero_of_injective a).trans
      (Ext.eq_zero_of_injective b).symm⟩) m).2 fun φ hφ => ?_
  have hK : ∀ q k : ℕ, Subsingleton (Ext.{u} (constZ X.toTopCat) (C.X q) (k + 1)) :=
    fun q k => @subsingleton_ext_of_isFlasque X.toTopCat _ k (C.X q)
      (isFlasque_toSheaf_internalHom (O := X.sheaf) F (Res.cocomplex.X q))
  have : PreservesFiniteColimits T := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits _
  have : T.PreservesHomology := inferInstance
  have hH : ∀ q k : ℕ, d < k + q →
      Subsingleton (Ext.{u} (constZ X.toTopCat) (C.homology q) k) :=
    fun q k hqk => Stacks.ExtCycles.subsingleton_ext_of_iso _ ((K.sc q).mapHomologyIso T).symm
      (subsingleton_ext_homology_cx_of_isRegular hX d hd F G hF Res q k hqk)
  let φAb : constZ X.toTopCat ⟶ C.X (m + 1) := (homConstAddEquiv _).symm (sectionOf ⊤ φ)
  have e : homConstAddEquiv _ φAb = sectionOf ⊤ φ := AddEquiv.apply_symm_apply _ _
  have hφAb : φAb ≫ C.d (m + 1) (m + 2) = 0 := by
    apply (homConstAddEquiv _).injective
    rw [homConstAddEquiv_comp, e, map_zero]
    change sectionOf ⊤ (φ ≫ Res.cocomplex.d (m + 1) (m + 2)) = 0
    rw [hφ, sectionOf_zero]
  obtain ⟨ψAb, hψAb⟩ := Stacks.ExtCycles.exists_comp_d_eq_of_subsingleton_ext_homology
    (constZ X.toTopCat) C d hK hH m hm φAb hφAb
  obtain ⟨ψ, hψ⟩ := sectionOf_top_surjective (A := F) (I := Res.cocomplex.X m)
    (homConstAddEquiv _ ψAb)
  refine ⟨ψ, sectionOf_top_injective ?_⟩
  have h := congrArg (homConstAddEquiv _) hψAb
  rwa [homConstAddEquiv_comp, ← hψ, e] at h

section Regular

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0FZ3] part (1).** Let `X` be a regular Noetherian scheme of dimension
`d < ∞`, let `F` be a coherent `𝒪_X`-module and `G` an arbitrary `𝒪_X`-module. Then
`Ext^n_X(F, G) = 0` for every `n > d`. -/
@[stacks 0FZ3 "part (1): on a regular Noetherian scheme of dimension d, Ext^n(F, G) = 0 for \
n > d, F coherent (G arbitrary)"]
theorem subsingleton_zExt_of_isRegular (X : Scheme.{u}) [IsNoetherian X] (hX : IsRegular X)
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (F G : X.Modules)
    (hF : F.IsCoherent) (n : ℤ) (hn : (d : ℤ) < n) : Subsingleton (Abelian.zExt F G n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by omega⟩
  let : HasExt.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    IsGrothendieckAbelian.hasExt _
  have h : Subsingleton (Abelian.Ext.{u} F G (m + 1)) :=
    subsingleton_ext_of_isRegular hX d hd F G hF m (by omega)
  exact (Abelian.Ext.homEquiv (X := F) (Y := G) (n := m + 1)).symm.subsingleton

/-- **[Stacks, Tag 0FZ3] part (2).** Let `X` be a regular Noetherian scheme of dimension
`d < ∞`. Let `K` and `L` be objects of `D^b_{Coh}(𝒪_X)` and let `a` be an integer. If
`H^i(K) = 0` for `i < a + d` and `H^i(L) = 0` for `i ≥ a`, then `Hom_X(K, L) = 0`. -/
@[stacks 0FZ3 "part (2): on a regular Noetherian scheme of dimension d, Hom(K, L) = 0 for \
K, L in D^b_Coh with H^i(K) = 0 for i < a + d and H^i(L) = 0 for i >= a"]
theorem subsingleton_hom_of_homology_separated_of_isRegular (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (K L : DerivedCategory X.Modules) (a : ℤ)
    (hKb : DerivedCategory.TStructure.t.bounded K)
    (hLb : DerivedCategory.TStructure.t.bounded L)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (hK : ∀ i : ℤ, i < a + d → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K))
    (hL : ∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) :
    Subsingleton (K ⟶ L) :=
  subsingleton_hom_of_homology_separated X hX d hd
    (fun F G hF _ n hn => subsingleton_zExt_of_isRegular X hX d hd F G hF n hn)
    K L a hKb hLb hKcoh hLcoh hK hL

/-- [Stacks, Tag 0FZ3] part (2) for every Noetherian scheme and every dimension, in the form of
`AlgebraicGeometry.SeparatedCohomologyHomVanishing`. -/
theorem forall_separatedCohomologyHomVanishing :
    ∀ (W : Scheme.{u}) [IsNoetherian W] (e : ℕ), SeparatedCohomologyHomVanishing W e :=
  fun W _ e hW hd K L hKb hLb hKcoh hLcoh a hK hL =>
    subsingleton_hom_of_homology_separated_of_isRegular W hW e hd K L a hKb hLb hKcoh hLcoh hK hL

end Regular

end AlgebraicGeometry

end
