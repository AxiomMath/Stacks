module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothProperHigherDirectImageLocallyConstantReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of locally constant sheaves along smooth proper morphisms

[Stacks, Proposition 0GLI]: let `f : X ⟶ S` be smooth and proper, `Λ` a Noetherian ring and `F`
a finite type, locally constant sheaf of `Λ`-modules on `X_étale` whose stalk at every geometric
point `x̄` is killed by an integer prime to the residue characteristic of `x̄`. Then every
`Rⁱ f_* F` is a finite type, locally constant sheaf of `Λ`-modules on `S_étale`.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_forall_smallEtaleStalkAb`: annihilation by an integer
  is detected on stalks.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_of_forall_mem_range`: finite type local
  constancy is local for étale coverings.
* `Stacks.EtaleCohomology.exists_isAffineOpen_nsmul_smallEtaleStalkAb_eq_zero`: a uniform
  annihilator, invertible on an affine neighbourhood of a point of the base.
* `isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper` (in
  `Stacks.EtaleCohomology`): the higher direct images of such an `F` along a smooth proper
  morphism are finite type and locally constant.

## References

* [Stacks Project, Tag 0GLI](https://stacks.math.columbia.edu/tag/0GLI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### A sheaf of modules killed on all stalks by `N` is killed by `N` -/

section Kill

/-- An integer killing every element of an abelian group kills every element of an isomorphic
one. -/
private theorem nsmul_eq_zero_of_iso {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) {N : ℕ}
    (h : ∀ a : A, N • a = 0) (b : B) : N • b = 0 := by
  have h1 := congrArg e.hom (h (e.inv b))
  rwa [map_nsmul, map_zero, ← ConcreteCategory.comp_apply, e.inv_hom_id,
    CategoryTheory.id_apply] at h1

variable (Λ : Type) [CommRing Λ]

/-- **Annihilation by an integer is detected on stalks.** If every stalk at a geometric point of
the abelian sheaf underlying a sheaf `F` of `Λ`-modules on `X_étale` is killed by `N`, then
`N • 𝟙 F = 0`. -/
theorem nsmul_id_eq_zero_of_forall_smallEtaleStalkAb {X : Scheme.{u}}
    (F : EtaleModules.{u, 0} Λ X) (N : ℕ)
    (h : ∀ (t : GeometricPoint X) (a : (smallEtaleStalkAb t.hom).obj
      ((etaleModuleForget Λ X).obj F)), N • a = 0) :
    N • 𝟙 F = 0 := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  let K := (etaleModuleForget Λ X).obj F
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hK' : N • 𝟙 (E.inverse.obj K) = 0 := by
    refine nsmul_id_eq_zero_of_forall_etaleStalk B ⟨X, hX⟩ (E.inverse.obj K) N fun t g => ?_
    exact nsmul_eq_zero_of_iso ((smallEtaleStalkAb t.hom).mapIso (E.counitIso.app K).symm ≪≫
      smallEtaleStalkAb_sheafEquiv_obj_iso B ⟨X, hX⟩ t (E.inverse.obj K)) (h t) g
  apply (etaleModuleForget Λ X).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  apply E.inverse.map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero, hK']

end Kill

/-! ### Finite type local constancy is local for étale coverings -/

section Local

attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse smallEtaleHasSheafifyModuleMax

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ]

/-- **Local constancy of finite type can be checked on an étale covering.** If every point of `Z`
lies in the image of an étale `w : W ⟶ Z` along which the inverse image of `G` is a finite type,
locally constant sheaf of `Λ`-modules, then so is `G`. -/
theorem isFiniteTypeLocallyConstant_of_forall_mem_range (Z : B.Scheme)
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ))
    (h : ∀ z : Z.obj, ∃ (W : B.Scheme) (w : W ⟶ Z), Etale (B.inclusion.map w) ∧
      z ∈ Set.range (B.inclusion.map w).base ∧
      IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B W.obj W.property)
        ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) w).obj G)) :
    IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B Z.obj Z.property) G := by
  classical
  choose W w hwe hz hW using h
  choose I V g hcov hV using fun z => hW z (SmallEtale.final B (W z).obj (W z).property)
  let Xp : (Σ z, I z) → SmallEtale B Z.obj Z.property := fun p =>
    ⟨Over.mk (Y := (V p.1 p.2).obj.left) ((V p.1 p.2).obj.hom ≫ w p.1), by
      have := hwe p.1
      have : Etale (B.inclusion.map (V p.1 p.2).obj.hom) := (V p.1 p.2).property
      show Etale (B.inclusion.map ((V p.1 p.2).obj.hom ≫ w p.1))
      rw [Functor.map_comp]
      infer_instance⟩
  let T := SmallEtale.final B Z.obj Z.property
  have hT : IsTerminal T := SmallEtale.finalIsTerminal B Z.obj Z.property
  refine isFiniteTypeLocallyConstant_of_cover (SmallEtale.topology B Z.obj Z.property) Λ hT G
    (f := fun p => hT.from (Xp p)) ?_ (fun p => ?_)
  · refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B Z.obj Z.property
      Xp (fun p => hT.from (Xp p)) fun x => ?_
    let x' : Z.obj := x
    obtain ⟨y, hy⟩ := hz x'
    obtain ⟨W', g', hg', hy'⟩ := SmallEtale.exists_mem_arrows_mem_range B (W x').obj
      (W x').property (hcov x') y
    obtain ⟨-, k, gi, ⟨i⟩, rfl⟩ := hg'
    obtain ⟨v, hv⟩ := hy'
    have hgi : (g x' i).hom.left = (V x' i).obj.hom :=
      (Category.comp_id ((g x' i).hom.left)).symm.trans (Over.w (g x' i).hom)
    have hfrom : (hT.from (Xp ⟨x', i⟩)).hom.left = (V x' i).obj.hom ≫ w x' :=
      (Category.comp_id _).symm.trans (Over.w (hT.from (Xp ⟨x', i⟩)).hom)
    refine ⟨⟨x', i⟩, (SmallEtale.toScheme B _ _).map k v, ?_⟩
    rw [hfrom]
    show (B.inclusion.map ((V x' i).obj.hom ≫ w x')) _ = x'
    have hv' : (B.inclusion.map (V x' i).obj.hom) ((SmallEtale.toScheme B _ _).map k v) = y := by
      rw [← hgi, ← hv, Functor.map_comp]
      rfl
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hv']
    exact hy
  · obtain ⟨E, hE, he⟩ := hV p.1 p.2
    refine ⟨E, hE, ?_⟩
    rw [nonempty_constantSheafIso_over_iff B (W p.1).obj (W p.1).property (V p.1 p.2)
      (ModuleCat.{u + 1} Λ) _ E] at he
    rw [nonempty_constantSheafIso_over_iff B Z.obj Z.property (Xp p) (ModuleCat.{u + 1} Λ) G E]
    obtain ⟨c⟩ := he
    exact ⟨c ≪≫ (smallEtaleSheafPullbackCompIso B (V p.1 p.2).obj.left (W p.1) Z
      (V p.1 p.2).obj.hom (w p.1) (ModuleCat.{u + 1} Λ)).app G⟩

end Local

/-! ### Stalks of a finite type locally constant sheaf near a point -/

section Stalks

variable (Λ : Type) [CommRing Λ]

/-- Over an étale `V ⟶ X` on which `F` is the constant sheaf on `E`, the abelian stalk of `F` at
any geometric point lifting to `V` is the abelian group underlying `E`. -/
theorem nonempty_smallEtaleStalkAb_iso_of_constant {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X)
    (V : X.Etale) (E : ModuleCat.{u + 1} Λ)
    (c : (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj F)
    (t : GeometricPoint X) (v : (Scheme.pointSmallEtale t.hom).fiber.obj V) :
    Nonempty ((smallEtaleStalkAb t.hom).obj ((etaleModuleForget Λ X).obj F) ≅
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E) := by
  let Φ := Scheme.pointSmallEtale t.hom
  let J' := X.smallEtaleTopology.over V
  have := ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ J'
  have := ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ J'
  exact ⟨((Φ.sheafFiberOverIso v AddCommGrpCat.{u + 1}).app _).symm ≪≫
    (Φ.over v).sheafFiber.mapIso
      ((sheafCompose J' (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso c.symm ≪≫
        (constantCommuteCompose J' (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app E) ≪≫
    (Sites.constantSheafFiberNatIso (Φ.over v)).app _⟩

/-- An integer prime to the characteristic of a field is nonzero in it. -/
theorem natCast_ne_zero_of_ringChar {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (h : ringChar K = 0 ∨ n.Coprime (ringChar K)) : ((n : ℕ) : K) ≠ 0 := by
  intro h0
  have hdvd : ringChar K ∣ n := (ringChar.spec K n).1 h0
  rcases h with h | h
  · rw [h] at hdvd
    exact hn.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  · have h1 : ringChar K = 1 := Nat.Coprime.eq_one_of_dvd h.symm hdvd
    exact CharP.ringChar_ne_one h1

/-- **Annihilators of the stalks of a finite type locally constant sheaf are locally constant.**
For every point `y` of `X` there are an open neighbourhood `O` of `y` and an integer `n > 0`,
nonzero in the residue field of `y`, killing the abelian stalk of `F` at every geometric point
of `X` lying over a point of `O`. -/
theorem exists_opens_nsmul_smallEtaleStalkAb_eq_zero {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (y : X) :
    ∃ (O : X.Opens) (n : ℕ), y ∈ O ∧ 0 < n ∧ ((n : ℕ) : X.residueField y) ≠ 0 ∧
      ∀ (t : GeometricPoint X), t.hom default ∈ O →
        ∀ a : (smallEtaleStalkAb t.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0 := by
  let yb := X.algClosedPoint y
  obtain ⟨I, V, g, hcov, hV⟩ := hF (Scheme.Etale.mk (𝟙 X))
  let Φ := Scheme.pointSmallEtale yb.hom
  let x0 : Φ.fiber.obj (Scheme.Etale.mk (𝟙 X)) := Over.homMk yb.hom (by simp)
  obtain ⟨W, k, hk, z, -⟩ := Φ.jointly_surjective _ hcov x0
  obtain ⟨-, k', -, ⟨i⟩, rfl⟩ := hk
  let v := Φ.fiber.map k' z
  obtain ⟨E, -, ⟨c⟩⟩ := hV i
  obtain ⟨e⟩ := nonempty_smallEtaleStalkAb_iso_of_constant Λ F (V i) E c yb v
  obtain ⟨n, hn, hchar, hkill⟩ := htors yb
  have hE := nsmul_eq_zero_of_iso e hkill
  have : UniversallyOpen (V i).hom := UniversallyOpen.of_flat (V i).hom
  refine ⟨⟨Set.range (V i).hom.base, (V i).hom.isOpenMap.isOpen_range⟩, n, ?_, hn, ?_, ?_⟩
  · let l0 : Spec (.of yb.residueField) ⟶ (V i).left := v.left
    have hv : l0 ≫ (V i).hom = yb.hom := Over.w v
    refine ⟨l0 (default : Spec (.of yb.residueField)), ?_⟩
    show (l0 ≫ (V i).hom) (default : Spec (.of yb.residueField)) = y
    rw [hv]
    exact X.algClosedPointHom_apply y _
  · refine fun h0 => natCast_ne_zero_of_ringChar hn hchar ?_
    have := congrArg (algebraMap (X.residueField y) (AlgebraicClosure (X.residueField y))) h0
    rwa [map_natCast, map_zero] at this
  · intro t ht a
    obtain ⟨x, hx⟩ := ht
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (V i).hom t.hom x hx
    let v' : (Scheme.pointSmallEtale t.hom).fiber.obj (V i) := Over.homMk l hl
    obtain ⟨e'⟩ := nonempty_smallEtaleStalkAb_iso_of_constant Λ F (V i) E c t v'
    exact nsmul_eq_zero_of_iso e'.symm hE a

/-- **A uniform annihilator over a neighbourhood of a point of the base.** For `f : X ⟶ S` proper
and `s : S` there are an affine open neighbourhood `U` of `s` and an integer `N > 0` invertible on
`U` killing the abelian stalk of `F` at every geometric point of `X` lying over `U`. -/
theorem exists_isAffineOpen_nsmul_smallEtaleStalkAb_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (s : S) :
    ∃ (U : S.Opens) (N : ℕ), s ∈ U ∧ IsAffineOpen U ∧ 0 < N ∧ IsUnit ((N : ℕ) : Γ(S, U)) ∧
      ∀ (t : GeometricPoint X), f (t.hom default) ∈ U →
        ∀ a : (smallEtaleStalkAb t.hom).obj ((etaleModuleForget Λ X).obj F), N • a = 0 := by
  classical
  choose O n hyO hn hn0 hkill using exists_opens_nsmul_smallEtaleStalkAb_eq_zero Λ F hF htors
  obtain ⟨T, hT⟩ := (f.isCompact_preimage_singleton s).elim_finite_subcover
    (fun y : f ⁻¹' {s} => (O y : Set X)) (fun y => (O y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyO y⟩)
  let N : ℕ := ∏ y ∈ T, n y
  have hN : 0 < N := Finset.prod_pos fun y _ => hn y
  let W : Set X := ⋃ y ∈ T, (O y : Set X)
  have hWo : IsOpen W := isOpen_biUnion fun y _ => (O y).isOpen
  have hC : IsClosed (f '' Wᶜ) := f.isClosedMap _ hWo.isClosed_compl
  have hsC : s ∉ f '' Wᶜ := fun ⟨x, hx, hxs⟩ => hx (hT hxs)
  have hmem : ∀ y : f ⁻¹' {s}, s ∈ S.basicOpen ((n y : ℕ) : Γ(S, ⊤)) := by
    intro y
    have h1 : y.1 ∈ X.basicOpen ((n y : ℕ) : Γ(X, ⊤)) := by
      rw [← X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y.1 trivial, map_natCast]
      exact hn0 y
    have h2 : f y.1 ∈ S.basicOpen ((n y : ℕ) : Γ(S, ⊤)) := by
      show y.1 ∈ f ⁻¹ᵁ S.basicOpen ((n y : ℕ) : Γ(S, ⊤))
      rwa [Scheme.preimage_basicOpen, map_natCast]
    exact (congrArg (· ∈ S.basicOpen ((n y : ℕ) : Γ(S, ⊤))) (show f y.1 = s from y.2)).mp h2
  have hprod : ∀ T' : Finset (f ⁻¹' {s}),
      s ∈ S.basicOpen (((∏ y ∈ T', n y : ℕ) : Γ(S, ⊤))) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => simp
    | insert y T' hy ih =>
      rw [Finset.prod_insert hy, Nat.cast_mul, Scheme.basicOpen_mul]
      exact ⟨hmem y, ih⟩
  let U₀ : S.Opens := S.basicOpen ((N : ℕ) : Γ(S, ⊤)) ⊓ ⟨(f '' Wᶜ)ᶜ, hC.isOpen_compl⟩
  have hsU₀ : s ∈ U₀ := ⟨hprod T, hsC⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, hUU₀⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hsU₀ U₀.isOpen
  refine ⟨U, N, hsU, hU, hN, ?_, ?_⟩
  · refine S.toRingedSpace.isUnit_of_isUnit_germ U _ fun x hx => ?_
    have h1 := (S.mem_basicOpen ((N : ℕ) : Γ(S, ⊤)) x trivial).1 (hUU₀ hx).1
    rwa [map_natCast] at h1 ⊢
  · intro t ht a
    have htW : t.hom default ∈ W := by_contra fun h => (hUU₀ ht).2 ⟨_, h, rfl⟩
    obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 htW
    obtain ⟨m, hm⟩ : n y ∣ N := Finset.dvd_prod_of_mem _ hyT
    show N • a = 0
    rw [hm, mul_comm, ← smul_smul, hkill y t hy a, smul_zero]

/-- An integer killing the abelian stalk of `F` at the geometric point `t ≫ g` kills the abelian
stalk of the inverse image of `F` along `g` at `t`. -/
theorem nsmul_smallEtaleStalkAb_inverseImage_eq_zero {X X' : Scheme.{u}} (g : X' ⟶ X)
    (F : EtaleModules.{u, 0} Λ X) (t : GeometricPoint X') (N : ℕ)
    (h : ∀ a : (smallEtaleStalkAb (t.hom ≫ g)).obj ((etaleModuleForget Λ X).obj F), N • a = 0)
    (a : (smallEtaleStalkAb t.hom).obj
      ((etaleModuleForget Λ X').obj ((etaleModuleInverseImage.{u, 0} Λ g).obj F))) :
    N • a = 0 := by
  let e : (smallEtaleStalkAb t.hom).obj
        ((etaleModuleForget Λ X').obj ((etaleModuleInverseImage.{u, 0} Λ g).obj F)) ≅
      (smallEtaleStalkAb (t.hom ≫ g)).obj ((etaleModuleForget Λ X).obj F) :=
    ((Scheme.pointSmallEtale t.hom).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app _ ≪≫
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
        ((etaleModuleStalkPullbackIso Λ g t.hom).app F) ≪≫
      (((Scheme.pointSmallEtale (t.hom ≫ g)).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F).symm
  exact nsmul_eq_zero_of_iso e.symm h a

end Stalks

/-! ### Higher direct images along a smooth proper morphism -/

section Main

attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse smallEtaleHasSheafifyModuleMax

/-- Let `f : X ⟶ S` be a smooth proper morphism of schemes, let `Λ` be a Noetherian ring and let
`F` be a finite type, locally constant sheaf of `Λ`-modules on
`X_étale` such that for every geometric point `x̄` of `X` the stalk `F_x̄` is annihilated by an
integer `n > 0` prime to the residue characteristic of `x̄`. Then `Rⁱ f_* F` is a finite type,
locally constant sheaf of `Λ`-modules on `S_étale` for every `i`.

Here `Rⁱ f_*` is the `i`-th right derived functor of the direct image of sheaves of `Λ`-modules
for the small étale topologies, `i : ℕ` (for `i < 0` it is zero); the stalk `F_x̄` is that of the
underlying abelian sheaf, and "prime to the residue characteristic" reads `n` coprime to the
characteristic of the residue field of `x̄`, a condition void in characteristic zero. -/
@[stacks 0GLI,
  sga "1 XIII 2.9" "special case",
  sga "4 XVI 2.1" "special case",
  sga "4 XVI 2.2" "Abelian torsion case",
  sga "7 I 0.1.5" "special case"]
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (Λ : Type) [CommRing Λ]
    [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (i : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived i).obj F) := by
  let B := BigEtaleSite.containing S
  have hS : B.Contains S := BigEtaleSite.contains_containing S
  have hX : B.Contains X := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS
  let SB : B.Scheme := B.obj S hS
  let G := ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived i).obj F
  have hFt : IsTorsionEtaleModule Λ X F :=
    torsionSheafProperty_of_forall_smallEtaleStalkAb _ fun t g =>
      let ⟨n, hn, _, h⟩ := htors t
      ⟨n, hn, h g⟩
  refine (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B SB Λ G).1 ?_
  refine isFiniteTypeLocallyConstant_of_forall_mem_range B Λ SB _ fun s => ?_
  obtain ⟨U, N, hsU, hU, hN, hNU, hkill⟩ :=
    exists_isAffineOpen_nsmul_smallEtaleStalkAb_eq_zero Λ f F hF htors s
  have hUB : B.Contains U.toScheme := Scheme.size_lt_of_isOpenImmersion U.ι hS
  let UB : B.Scheme := B.obj U.toScheme hUB
  let w : UB ⟶ SB := ObjectProperty.homMk U.ι
  have hXU : B.Contains (pullback f U.ι) :=
    Scheme.size_lt_of_isOpenImmersion (pullback.fst f U.ι) hX
  let XUB : B.Scheme := B.obj (pullback f U.ι) hXU
  let fU : XUB.obj ⟶ UB.obj := pullback.snd f U.ι
  have sq : IsPullback (pullback.fst f U.ι) fU f U.ι := IsPullback.of_hasPullback f U.ι
  have : IsAffine UB.obj := hU
  let FU := (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f U.ι)).obj F
  have hFU : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} XUB.obj.smallEtaleTopology Λ FU :=
    isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ (pullback.fst f U.ι) F hF
  have hNFU : N • 𝟙 FU = 0 :=
    nsmul_id_eq_zero_of_forall_smallEtaleStalkAb Λ FU N fun t a =>
      nsmul_smallEtaleStalkAb_inverseImage_eq_zero Λ (pullback.fst f U.ι) F t N
        (hkill (GeometricPoint.mk _ (t.hom ≫ pullback.fst f U.ι)) (by
          show (t.hom ≫ pullback.fst f U.ι ≫ f) default ∈ U
          rw [sq.w]
          show U.ι ((t.hom ≫ fU) default) ∈ U
          exact ((t.hom ≫ fU) default).2)) a
  have hunit : IsUnit ((N : ℕ) : Γ(UB.obj, ⊤)) := by
    have h := hNU.map (U.topIso.inv).hom
    rwa [map_natCast] at h
  obtain ⟨e⟩ := nonempty_inverseImage_rightDerived_iso_of_isProper Λ f sq F hFt i
  have hGU : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} UB.obj.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map w)).obj G) :=
    ObjectProperty.prop_of_iso _ e.symm <|
      isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_isAffine B Λ N hN
        (X := XUB) (S := UB) fU hunit FU hFU hNFU i
  refine ⟨UB, w, inferInstanceAs (Etale U.ι), ⟨⟨s, hsU⟩, rfl⟩, ?_⟩
  exact IsFiniteTypeLocallyConstant.of_iso Λ _ (etaleModulesToSmallEtalePullbackIso B Λ w G)
    ((SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B UB Λ _).2 hGU)

end Main

end Stacks.EtaleCohomology

end
