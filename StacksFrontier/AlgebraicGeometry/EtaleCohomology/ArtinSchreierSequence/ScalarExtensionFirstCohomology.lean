module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionDegreeOne
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.FibreDims
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# `H¹(X, 𝐙/p𝐙)` does not change under extension of an algebraically closed ground field

Let `X` be proper over an algebraically closed field `k` of characteristic `p > 0`, covered by two
affine opens, and let `k'/k` be an extension of algebraically closed fields. Then restriction
along the projection `X_{k'} ⟶ X` is a bijection `H¹(X, 𝐙/p𝐙) ⟶ H¹(X_{k'}, 𝐙/p𝐙)`. This is the
degree-one case of [Stacks, Tag 0A3P] (2) for such `X`.

The proof is the source's: `Stacks.ArtinSchreier.bijective_of_frobenius_base_change` reduces the
statement to the base-change properties of the map `β : H¹(X, 𝒪_X) ⟶ H¹(X_{k'}, 𝒪_{X_{k'}})`.
Here `β` is read on the étale side: it is the restriction of the étale cohomology of `𝐆_a`
followed by pulling functions back (`Stacks.ArtinSchreier.additiveRestriction`), transported by
the comparison of [Stacks, Tag 03P2]. That makes its compatibility with the Frobenius and with
the inclusion `𝐙/p𝐙 ⟶ 𝐆_a` a consequence of naturality, its semilinearity a consequence of the
`k`-linearity of the comparison, and its spanning property the Mayer–Vietoris computation
`Stacks.ArtinSchreier.exists_sum_additiveRestriction_one`; injectivity follows from spanning and
the equality of dimensions given by flat base change ([Stacks, Tag 02KH] over a field,
`AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`).

## Main results

* `Stacks.ArtinSchreier.injective_of_span_range_eq_top_of_finrank_eq`: a semilinear map with
  spanning image between spaces of the same finite dimension is injective.
* `Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod_one_of_cover`: the
  bijectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

/-! ### Linear algebra -/

/-- **A semilinear map whose image spans a space of the same finite dimension is injective.**
Let `β : V ⟶ V'` be additive and semilinear over a field homomorphism `φ : k ⟶ k'`, with `V`
finite-dimensional over `k`, `V'` of the same dimension over `k'`, and the image of `β` spanning
`V'`. The images of a basis of `V` span `V'` and are as many as its dimension, hence are
linearly independent, and a vector in the kernel has coordinates killed by the injective `φ`. -/
theorem injective_of_span_range_eq_top_of_finrank_eq {k k' : Type*} [Field k] [Field k']
    (φ : k →+* k') {V V' : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup V'] [Module k' V'] (β : V →+ V') (hβ : ∀ (c : k) (v : V), β (c • v) = φ c • β v)
    (hspan : Submodule.span k' (Set.range β) = ⊤)
    (hdim : Module.finrank k' V' = Module.finrank k V) : Function.Injective β := by
  classical
  let b := Module.finBasis k V
  have hsum : ∀ v : V, β v = ∑ i, φ (b.repr v i) • β (b i) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hβ _ _
  have hspan' : ⊤ ≤ Submodule.span k' (Set.range fun i => β (b i)) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    rw [hsum v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have : Module.Finite k' V' := by
    refine ⟨?_⟩
    have h := Submodule.fg_span (R := k') (Set.finite_range fun i => β (b i))
    rwa [top_le_iff.mp hspan'] at h
  have hli : LinearIndependent k' (fun i => β (b i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan' (by simp [hdim])
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : ∑ i, φ (b.repr v i) • β (b i) = 0 := by rw [← hsum v]; exact hv
  have hz := Fintype.linearIndependent_iff.mp hli (fun i => φ (b.repr v i)) h0
  refine b.repr.map_eq_zero_iff.mp ?_
  ext i
  simpa using hz i

/-! ### The restriction map on the cohomology of `𝐆_a` and the maps of the sequence -/

section Naturality

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The restriction map on the cohomology of `𝐆_a` commutes with maps intertwined by the
inverse-image comparison.** -/
theorem additiveRestriction_sheafH_map {n : ℕ}
    {m : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X}
    {m' : additiveSheaf.{u, u + 1} Y ⟶ additiveSheaf.{u, u + 1} Y}
    (h : (etaleAbelianInverseImage.{u, 0} g).map m ≫ additiveInverseImageComparison.{u, u + 1} g =
      additiveInverseImageComparison.{u, u + 1} g ≫ m')
    (x : Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) n) :
    additiveRestriction g n (Sheaf.H.map m n x) = Sheaf.H.map m' n (additiveRestriction g n x) := by
  simp only [additiveRestriction_apply, Sheaf.H.map_apply]
  rw [etaleCohomologyRestrictionMap_comp_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, h]

/-- **Restriction carries the inclusion of `𝐙/p𝐙` in `𝐆_a` to the inclusion**, through the
identification `g^{-1} 𝐙/p𝐙 ≅ 𝐙/p𝐙`. -/
theorem additiveRestriction_sheafH_map_zmodSheafHom {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) {n : ℕ} (x : Sheaf.H.{u + 1} (etaleConstantZMod X p) n) :
    additiveRestriction g n (Sheaf.H.map (zmodSheafHom.{u, u + 1} X hX) n x) =
      Sheaf.H.map (zmodSheafHom.{u, u + 1} Y hY) n
        (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
          ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))) n
          (etaleCohomologyRestrictionMap.{u, 0, u + 1} g (etaleConstantZMod X p) n x)) := by
  simp only [additiveRestriction_apply, Sheaf.H.map_apply]
  have hι : (etaleAbelianInverseImage.{u, 0} g).map (zmodSheafHom.{u, u + 1} X hX) ≫
      additiveInverseImageComparison.{u, u + 1} g =
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))).hom ≫
        zmodSheafHom.{u, u + 1} Y hY :=
    inverseImage_zmodSheafHom_comp_additiveInverseImageComparison.{u, u + 1} g hX
  rw [etaleCohomologyRestrictionMap_comp_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    hι]
  change _ = ((etaleCohomologyRestrictionMap.{u, 0, u + 1} g (etaleConstantZMod X p) n x).comp
    (Ext.mk₀ _) (add_zero n)).comp (Ext.mk₀ _) (add_zero n)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end Naturality

/-! ### Scalars along the scalar extension -/

section Scalars

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **The pullback to `X_{k'}` of the scalar `c ∈ k` is the scalar `c ∈ k'`.** -/
theorem appTop_scalarExtensionFst_baseScalarSection (c : k) :
    (scalarExtensionFst k k' f).appTop.hom (baseScalarSection k f c) =
      baseScalarSection k' (scalarExtensionStructure f) (algebraMap k k' c) := by
  change (f.appLE ⊤ ⊤ _ ≫ (scalarExtensionFst k k' f).appTop).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c) =
    (scalarExtensionStructure f).appLE ⊤ ⊤ _
      ((Scheme.ΓSpecIso (.of k')).inv.hom (algebraMap k k' c))
  rw [Stacks.Descent.appLE_top_top, Stacks.Descent.appLE_top_top, ← Scheme.Hom.comp_appTop,
    pullback.condition, Scheme.Hom.comp_appTop]
  change ((scalarExtensionStructure f).appTop.hom
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop).hom
      c)) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Scalars

/-! ### The bijectivity -/

/-- The Frobenius of a top-degree Frobenius comparison is `equiv (φ y) + equiv y` on `equiv y`. -/
private theorem frobenius_equiv_eq {p : ℕ} {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {Ga : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {φ : Ga ⟶ Ga} {d : ℕ}
    (cmp : TopDegreeFrobeniusComparison.{u + 1} p k f Ga φ d) (y : Sheaf.H.{u + 1} Ga d) :
    cmp.frobenius (cmp.equiv y) = cmp.equiv (Sheaf.H.map φ d y) + cmp.equiv y :=
  eq_add_of_sub_eq (cmp.equiv_map y).symm

section Bijective

variable {p : ℕ} (hp : p.Prime) (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
  (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The comparison of [Stacks, Tag 03P2] for `X` in degree one. -/
local notation "𝔠" => constantSequenceFrobeniusComparison hp k f 1
/-- The comparison of [Stacks, Tag 03P2] for `X_{k'}` in degree one. -/
local notation "𝔠'" => constantSequenceFrobeniusComparison hp k' (scalarExtensionStructure f) 1
/-- `p` vanishes on `X`. -/
local notation "𝔥" => natCast_eq_zero_of_charP k p f
/-- `p` vanishes on `X_{k'}`. -/
local notation "𝔥'" => natCast_eq_zero_of_charP k' p (scalarExtensionStructure f)

include hp in
/-- **[Stacks, Tag 0A3P] (2) in degree one, for a proper scheme covered by two affine opens.**
Let `X` be proper over an algebraically closed field `k` of characteristic `p > 0`, covered by
two affine opens `U`, `V` with affine intersection, and let `k'/k` be an extension of
algebraically closed fields. Then restriction along `X_{k'} ⟶ X` is a bijection
`H¹(X, 𝐙/p𝐙) ⟶ H¹(X_{k'}, 𝐙/p𝐙)`.

This is `Stacks.ArtinSchreier.bijective_of_frobenius_base_change` with `β` the restriction of
the cohomology of `𝐆_a` read through the comparison of [Stacks, Tag 03P2]: semilinear because the
comparison is linear, compatible with the Frobenius and with `𝐙/p𝐙 ⟶ 𝐆_a` by naturality,
spanning by the Mayer–Vietoris computation, and injective by spanning and flat base change of
dimensions. -/
theorem bijective_etaleCohomologyRestrictionMap_constantZMod_one_of_cover (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV' : IsAffineOpen (U ⊓ V)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' f)
      (etaleConstantZMod X p) 1) := by
  have : CharP k' p := charP_of_injective_algebraMap' k p
  have : IsProper (scalarExtensionStructure (k' := k') f) := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine (V : Scheme.{u}) := hV
  have : IsAffine ((U ⊓ V : X.Opens) : Scheme.{u}) := hUV'
  have : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := inferInstance
  have : IsAffineHom (scalarExtensionFst k k' f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).flip this
  -- the two comparisons of [Stacks, Tag 03P2], and the restriction map on `𝐆_a`
  let R := additiveRestriction (scalarExtensionFst k k' f) 1
  have hsmul : ∀ (c : k) x, (𝔠).equiv
      (Sheaf.H.map (additiveSmul.{u, u + 1} X (baseScalarSection k f c)) 1 x) =
      c • (𝔠).equiv x :=
    topDegreeFrobeniusComparison_equiv_additiveSmul hp k f 1
  have hsmul' : ∀ (c : k') x, (𝔠').equiv
        (Sheaf.H.map (additiveSmul.{u, u + 1} (scalarExtension k k' f)
          (baseScalarSection k' (scalarExtensionStructure f) c)) 1 x) =
      c • (𝔠').equiv x :=
    topDegreeFrobeniusComparison_equiv_additiveSmul hp k' (scalarExtensionStructure f) 1
  let β : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1 →+
      cohomologyOverField k' (scalarExtensionStructure f)
        (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf) 1 :=
    (𝔠').equiv.toAddMonoidHom.comp (R.comp (𝔠).equiv.symm.toAddMonoidHom)
  have hβequiv : ∀ x, β ((𝔠).equiv x) = (𝔠').equiv (R x) := fun x =>
    congrArg (fun z => (𝔠').equiv (R z)) ((𝔠).equiv.symm_apply_apply x)
  -- semilinearity
  have hβ : ∀ (c : k) v, β (c • v) = algebraMap k k' c • β v := by
    intro c v
    have h1 : (𝔠).equiv.symm (c • v) = Sheaf.H.map
        (additiveSmul.{u, u + 1} X (baseScalarSection k f c)) 1 ((𝔠).equiv.symm v) :=
      (𝔠).equiv.injective (((𝔠).equiv.apply_symm_apply _).trans
        ((congrArg (c • ·) ((𝔠).equiv.apply_symm_apply v)).symm.trans (hsmul c _).symm))
    have hsm : (etaleAbelianInverseImage.{u, 0} (scalarExtensionFst k k' f)).map
        (additiveSmul.{u, u + 1} X (baseScalarSection k f c)) ≫
          additiveInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' f) =
        additiveInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' f) ≫
          additiveSmul.{u, u + 1} _
            (baseScalarSection k' (scalarExtensionStructure f) (algebraMap k k' c)) := by
      rw [← appTop_scalarExtensionFst_baseScalarSection]
      exact inverseImage_additiveSmul_comp_additiveInverseImageComparison.{u, u + 1} _ _
    exact (congrArg (fun z => (𝔠').equiv (R z)) h1).trans
      ((congrArg (𝔠').equiv (additiveRestriction_sheafH_map _ hsm _)).trans (hsmul' _ _))
  -- spanning
  have hspan : Submodule.span k' (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro y' _
    obtain ⟨n, x, c, hy⟩ := exists_sum_additiveRestriction_one f U V hUV ((𝔠').equiv.symm y')
    have : y' = ∑ i, c i • β ((𝔠).equiv (x i)) :=
      ((𝔠').equiv.apply_symm_apply y').symm.trans ((congrArg (𝔠').equiv hy).trans
        ((map_sum (𝔠').equiv _ _).trans (Finset.sum_congr rfl fun i _ =>
          (hsmul' (c i) _).trans (congrArg (c i • ·) (hβequiv (x i)).symm))))
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  -- dimensions and injectivity
  have hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f (SheafOfModules.unit X.ringCatSheaf) 1
  have hdim : Module.finrank k' (cohomologyOverField k' (scalarExtensionStructure f)
        (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf) 1) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    ((Stacks.FibreCohomology.cohomologyOverFieldMapIso k' (scalarExtensionStructure f)
      (Scheme.Modules.pullbackUnitIso (scalarExtensionFst k k' f)) 1).toLinearEquiv.finrank_eq
      ).symm.trans (finrank_cohomologyOverField_baseChange_field k k' (scalarExtensionFst k k' f)
        (scalarExtensionStructure f) f
        (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        (Scheme.unitModule X) 1)
  have hinj := injective_of_span_range_eq_top_of_finrank_eq (algebraMap k k') β hβ hspan hdim
  -- the Frobenius
  have hfrob : ∀ v, β ((𝔠).frobenius v) = (𝔠').frobenius (β v) := by
    intro v
    obtain ⟨x, rfl⟩ := (𝔠).equiv.surjective v
    have hAS : (etaleAbelianInverseImage.{u, 0} (scalarExtensionFst k k' f)).map
          (artinSchreierMap.{u, u + 1} X hp 𝔥) ≫
          additiveInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' f) =
        additiveInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' f) ≫
          artinSchreierMap.{u, u + 1} _ hp 𝔥' :=
      inverseImage_artinSchreierMap_comp_additiveInverseImageComparison.{u, u + 1} _ hp 𝔥
    rw [frobenius_equiv_eq, map_add, hβequiv, hβequiv]
    exact (congrArg (fun z => (𝔠').equiv z + _) (additiveRestriction_sheafH_map _ hAS _)).trans
      (frobenius_equiv_eq (𝔠') _).symm
  -- the inclusion of `𝐙/p𝐙`
  let ι := (etaleAbelianInverseImageConstantIso.{u, 0} (scalarExtensionFst k k' f)).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))
  let γ : Sheaf.H.{u + 1} (etaleConstantZMod X p) 1 →+
      Sheaf.H.{u + 1} (etaleConstantZMod (scalarExtension k k' f) p) 1 :=
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr ι 1).toAddMonoidHom.comp
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' f)
        (etaleConstantZMod X p) 1)
  have hγ : ∀ x, artinSchreierComparison k' (scalarExtensionStructure f)
      (constantArtinSchreierSequenceDatum _ hp 𝔥') 1 𝔠' (γ x) =
      β (artinSchreierComparison k f (constantArtinSchreierSequenceDatum X hp 𝔥) 1 𝔠 x) :=
    fun x => by
      have hA : artinSchreierComparison k f (constantArtinSchreierSequenceDatum X hp
          𝔥) 1 𝔠
          x = (𝔠).equiv
            (Sheaf.H.map (zmodSheafHom.{u, u + 1} X 𝔥) 1 x) := rfl
      have hA' : artinSchreierComparison k' (scalarExtensionStructure f)
          (constantArtinSchreierSequenceDatum _ hp
            𝔥') 1
          𝔠' (γ x) =
          (𝔠').equiv
            (Sheaf.H.map (zmodSheafHom.{u, u + 1} _
              𝔥') 1
              (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr ι 1
                (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' f)
                  (etaleConstantZMod X p) 1 x))) := rfl
      rw [hA, hA', hβequiv (Sheaf.H.map (zmodSheafHom.{u, u + 1} X
        𝔥) 1 x)]
      exact congrArg _ (additiveRestriction_sheafH_map_zmodSheafHom (scalarExtensionFst k k' f)
        𝔥
        𝔥' x).symm
  have key : Function.Bijective γ := by
    refine bijective_of_frobenius_base_change.{u + 1, u} k k' (algebraMap k k') f
      (scalarExtensionStructure f) (constantArtinSchreierSequenceDatum X hp 𝔥)
      (constantArtinSchreierSequenceDatum (scalarExtension k k' f) hp 𝔥') 1 hp.pos
      (constantSequenceFrobeniusComparison.{u + 1} hp k f)
      (constantSequenceFrobeniusComparison.{u + 1} hp k' (scalarExtensionStructure f)) β ?_
      ?_ ?_ ?_ γ ?_
    · exact hβ
    · exact hinj
    · exact hspan
    · exact hfrob
    · exact hγ
  exact (Function.Bijective.of_comp_iff'
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr ι 1).bijective _).mp key

end Bijective

end Stacks.ArtinSchreier

end
