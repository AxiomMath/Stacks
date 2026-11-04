module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffIndexEmptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Noetherian approximation of a proper flat family over an affine base

Let `T` be an affine object of the big fppf site of the terminal scheme, with ring of global
functions `R = Γ(T)`. Then `R` is the directed union of its finitely generated `ℤ`-subalgebras
`R_λ`, which are Noetherian, and `T = lim Spec R_λ` inside the site. A finitely presented, flat
and proper algebraic space `X ⟶ T` is the base change of a finitely presented, flat and proper
algebraic space `X_λ ⟶ Spec R_λ` for some `λ`, and the base changes `X_μ = X_λ ×_{T_λ} T_μ`,
`μ ≥ λ`, form a descent situation (Stacks 09RH) with limit `X` whose charts are bounded
(`AlgebraicGeometry.Space.ChartsBounded`). This is the reduction to a Noetherian base of the
proof of Stacks 0A1P and Stacks 0CTM.

## Main definitions

* `AlgebraicGeometry.BigAffineFppf.fgStageDiagram`: the system `λ ↦ Spec R_λ` of affine objects
  of the site, indexed by the finitely generated `ℤ`-subalgebras of `R` ordered by inclusion.
* `AlgebraicGeometry.BigAffineFppf.fgStageCone`: the cone with vertex `T` over it.

## Main results

* `AlgebraicGeometry.BigAffineFppf.isLimit_toScheme_mapCone_fgStageCone`: `T = lim Spec R_λ`.
* `AlgebraicGeometry.BigAffineFppf.chartsBounded_yonedaStageSystem`: the system of presheaves
  represented by the `Spec R_μ`, `μ ≥ λ`, has bounded charts, although its index may be larger
  than the cofinality of the cutoff.
* `AlgebraicGeometry.Space.exists_descentSituation_noetherianApproximation`: the statement
  above.

## Implementation notes

The descent of the family to a stage is
`AlgebraicGeometry.properFlatFamilyDescendsAlongAffineLimit`, which needs no bound on the index.
The approximating system is indexed by the finitely generated subalgebras containing that
stage, so that every stage of the descent situation carries a finitely presented, flat and
proper morphism to a Noetherian affine scheme.

## References

* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.BigAffineFppf

variable {B : BigFppfSite.{u}} (T : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal)

/-- The ring of global functions of an affine object of the site. -/
noncomputable abbrev globalRing : CommRingCat.{u} :=
  Γ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj T, ⊤)

/-- The finitely generated `ℤ`-subalgebras of the ring of global functions, ordered by
inclusion. -/
noncomputable abbrev FgIndex : Type u := {A : Subalgebra ℤ (globalRing T) // A.FG}

/-- The finitely generated subalgebras are directed: two of them lie in their supremum, which is
again finitely generated. -/
instance : IsDirectedOrder (FgIndex T) :=
  ⟨fun μ ν => ⟨⟨μ.val ⊔ ν.val, μ.2.sup ν.2⟩, (le_sup_left : μ.val ≤ _),
    (le_sup_right : ν.val ≤ _)⟩⟩

/-- There is a finitely generated subalgebra, namely `⊥`. -/
instance : Nonempty (FgIndex T) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The finitely generated `ℤ`-subalgebras of `Γ(T)` as a diagram of rings, the arrows being the
inclusions. -/
noncomputable def fgRingDiagram : FgIndex T ⥤ CommRingCat.{u} where
  obj μ := CommRingCat.of μ.val
  map {μ ν} f := CommRingCat.ofHom
    (Subalgebra.inclusion (show μ.val ≤ ν.val from leOfHom f)).toRingHom

/-- The cocone on `AlgebraicGeometry.BigAffineFppf.fgRingDiagram` with vertex `Γ(T)`, its legs
the inclusions. -/
noncomputable def fgRingCocone : Cocone (fgRingDiagram T) where
  pt := globalRing T
  ι := { app μ := CommRingCat.ofHom μ.val.val.toRingHom }

/-- **`Γ(T)` is the filtered colimit of its finitely generated `ℤ`-subalgebras, as a ring.** The
map out of `Γ(T)` is `Subalgebra.iSupLift` at the directed family, whose supremum is `⊤`, a ring
map being the same as a `ℤ`-algebra map; uniqueness is checked at a single element on the
subalgebra it generates. -/
noncomputable def isColimit_fgRingCocone : IsColimit (fgRingCocone T) := by
  classical
  have hdir : Directed (· ≤ ·) (fun μ : FgIndex T => μ.val) :=
    fun μ ν => ⟨⟨μ.val ⊔ ν.val, μ.2.sup ν.2⟩, le_sup_left, le_sup_right⟩
  have htop : (⨆ μ : FgIndex T, μ.val) = ⊤ :=
    eq_top_iff.mpr fun x _ => (le_iSup (fun μ : FgIndex T => μ.val)
      ⟨Algebra.adjoin ℤ ({x} : Finset (globalRing T)), Subalgebra.fg_adjoin_finset _⟩)
        (Algebra.subset_adjoin (by simp))
  let φ (s : Cocone (fgRingDiagram T)) (μ : FgIndex T) : μ.val →ₐ[ℤ] s.pt :=
    { toRingHom := (s.ι.app μ).hom
      commutes' := fun r => congrArg (· r)
        (RingHom.ext_int ((s.ι.app μ).hom.comp (algebraMap ℤ μ.val)) (algebraMap ℤ s.pt)) }
  have hcompat (s : Cocone (fgRingDiagram T)) (μ ν : FgIndex T) (h : μ.val ≤ ν.val) :
      φ s μ = (φ s ν).comp (Subalgebra.inclusion h) := by
    ext x
    exact (ConcreteCategory.congr_hom (s.w (homOfLE h)) x).symm
  let lift (s : Cocone (fgRingDiagram T)) : globalRing T →ₐ[ℤ] s.pt :=
    (Subalgebra.iSupLift (B := (s.pt : Type u)) (fun μ : FgIndex T => μ.val) hdir
      (φ s) (fun μ ν h => hcompat s μ ν h) ⊤
      htop.ge).comp Algebra.toTop
  have lift_val (s : Cocone (fgRingDiagram T)) (μ : FgIndex T) (x : μ.val) :
      lift s x.val = (s.ι.app μ).hom x :=
    Subalgebra.iSupLift_inclusion (fun μ : FgIndex T => μ.val) (dir := hdir)
      (hf := fun μ ν h => hcompat s μ ν h) (B := (s.pt : Type u))
      (f := φ s) x le_top
  refine ⟨fun s => CommRingCat.ofHom (lift s).toRingHom, fun s μ => ?_, fun s m hm => ?_⟩
  · ext x
    exact lift_val s μ x
  · ext x
    let μ : FgIndex T :=
      ⟨Algebra.adjoin ℤ ({x} : Finset (globalRing T)), Subalgebra.fg_adjoin_finset _⟩
    let x' : μ.val :=
      ⟨x, Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self _))⟩
    exact (ConcreteCategory.congr_hom (hm μ) x').trans (lift_val s μ x').symm

/-- The spectrum of a finitely generated subalgebra of `Γ(T)` is no larger than `T`. -/
theorem size_spec_fgIndex_le (μ : FgIndex T) :
    (Spec (CommRingCat.of μ.val)).size ≤
      ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj T).size := by
  rw [Scheme.size_Spec, Scheme.size_of_isAffine]
  exact max_le_max le_rfl (mk_le_of_injective Subtype.val_injective)

/-- The spectrum of a finitely generated subalgebra of `Γ(T)` lies in the site: its size is at
most that of `T`. -/
theorem contains_spec_fgIndex (μ : (FgIndex T)) : B.Contains (Spec (CommRingCat.of μ.val)) :=
  (size_spec_fgIndex_le T μ).trans_lt T.obj.left.property

/-- The stage `Spec R_μ` as an affine object of the site. -/
noncomputable def fgStage (μ : (FgIndex T)) : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal :=
  ⟨BigFppfOver.mk B _ _ ((contains_spec_fgIndex T) μ) (terminal.from _),
    (inferInstance : IsAffine (Spec (CommRingCat.of μ.val)))⟩

/-- **The approximating system** `μ ↦ Spec R_μ` of affine objects of the site. -/
noncomputable def fgStageDiagram :
    (FgIndex T)ᵒᵖ ⥤ BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal where
  obj μ := (fgStage T) μ.unop
  map {μ ν} f := ObjectProperty.homMk (BigFppfOver.homMk B _ _ ((contains_spec_fgIndex T) ν.unop)
    (terminal.from _) (Spec.map ((fgRingDiagram T).map f.unop)) (terminal.hom_ext _ _))
  map_id μ := by
    apply ObjectProperty.hom_ext
    apply BigFppfOver.map_toScheme_injective
    change Spec.map ((fgRingDiagram T).map (𝟙 μ.unop)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Spec.map_id]
  map_comp {μ ν ρ} f g := by
    apply ObjectProperty.hom_ext
    apply BigFppfOver.map_toScheme_injective
    change Spec.map ((fgRingDiagram T).map (g.unop ≫ f.unop)) =
      Spec.map ((fgRingDiagram T).map f.unop) ≫ Spec.map ((fgRingDiagram T).map g.unop)
    rw [CategoryTheory.Functor.map_comp, Spec.map_comp]

/-- The cone with vertex `T` over the approximating system, its legs the morphisms
`T ≅ Spec Γ(T) ⟶ Spec R_μ`. -/
noncomputable def fgStageCone : Cone (fgStageDiagram T) where
  pt := T
  π :=
    { app μ := ObjectProperty.homMk (BigFppfOver.homMk B _ _ ((contains_spec_fgIndex T) μ.unop)
        (terminal.from _) (((BigAffineFppf.toScheme B _ _).obj T).isoSpec.hom ≫
          Spec.map ((fgRingCocone T).ι.app μ.unop)) (terminal.hom_ext _ _))
      naturality μ ν f := by
        apply ObjectProperty.hom_ext
        apply BigFppfOver.map_toScheme_injective
        change ((BigAffineFppf.toScheme B _ _).obj T).isoSpec.hom ≫
            Spec.map ((fgRingCocone T).ι.app ν.unop) =
          (𝟙 _ ≫ ((BigAffineFppf.toScheme B _ _).obj T).isoSpec.hom ≫
            Spec.map ((fgRingCocone T).ι.app μ.unop)) ≫ Spec.map ((fgRingDiagram T).map f.unop)
        rw [Category.id_comp, Category.assoc]
        exact congrArg (_ ≫ ·) ((congrArg Spec.map ((fgRingCocone T).w f.unop).symm).trans
          (Spec.map_comp _ _)) }

/-- The underlying schemes of the approximating system are the spectra of the subalgebras. -/
noncomputable def fgStageDiagramToSchemeIso :
    (fgRingDiagram T).op ⋙ Scheme.Spec ≅
      (fgStageDiagram T) ⋙ BigAffineFppf.toScheme B (⊤_ Scheme.{u}) B.contains_terminal :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- **`T = lim Spec R_μ`.** The spectrum functor turns the colimit `Γ(T) = colim R_μ` into a
limit of schemes, and `T ≅ Spec Γ(T)` as `T` is affine. -/
noncomputable def isLimit_toScheme_mapCone_fgStageCone :
    IsLimit ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).mapCone
      (fgStageCone T)) :=
  let hS := isLimitOfPreserves Scheme.Spec (isColimit_fgRingCocone T).op
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv (fgStageDiagramToSchemeIso T) _).symm hS)
    (Cones.ext ((BigAffineFppf.toScheme B _ _).obj T).isoSpec.symm fun μ => by
      change Spec.map ((fgRingCocone T).ι.app μ.unop) ≫ 𝟙 _ = _ ≫
        ((BigAffineFppf.toScheme B _ _).obj T).isoSpec.hom ≫
          Spec.map ((fgRingCocone T).ι.app μ.unop)
      rw [Category.comp_id]
      exact (Iso.inv_hom_id_assoc _ _).symm)

/-- Every stage of the approximating system is Noetherian, being of finite type over `ℤ`. -/
theorem isNoetherianRing_fgStage (μ : (FgIndex T)) :
    IsNoetherianRing Γ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj
      ((fgStage T) μ), ⊤) := by
  have : Algebra.FiniteType ℤ μ.val := μ.val.fg_iff_finiteType.mp μ.property
  have : IsNoetherianRing μ.val := Algebra.FiniteType.isNoetherianRing ℤ μ.val
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.ΓSpecIso (CommRingCat.of μ.val)).commRingCatIsoToRingEquiv.symm

/-! ### The approximating system above a stage -/

variable (μ₀ : FgIndex T)

/-- The finitely generated `ℤ`-subalgebras of `Γ(T)` containing `μ₀`. -/
abbrev FgIndexAbove : Type u := {μ : FgIndex T // μ₀ ≤ μ}

/-- The finitely generated subalgebras containing `μ₀` are directed. -/
instance : IsDirectedOrder (FgIndexAbove T μ₀) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩

/-- There is a finitely generated subalgebra containing `μ₀`, namely `μ₀` itself. -/
instance : Nonempty (FgIndexAbove T μ₀) := ⟨⟨μ₀, le_rfl⟩⟩

/-- The inclusion of the subalgebras containing `μ₀` among all finitely generated ones. -/
noncomputable def fgIndexAboveInclusion : FgIndexAbove T μ₀ ⥤ FgIndex T :=
  Monotone.functor (f := Subtype.val) fun _ _ h => h

/-- The subalgebras containing `μ₀` are cofinal. -/
instance : (fgIndexAboveInclusion T μ₀).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun μ => by
      obtain ⟨c, h₁, h₂⟩ := exists_ge_ge μ μ₀
      exact ⟨⟨c, h₂⟩, ⟨homOfLE h₁⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

/-- **The approximating system of presheaves** `μ ↦ h_{Spec R_μ}`, `μ ≥ μ₀`. -/
noncomputable def yonedaStageSystem : (FgIndexAbove T μ₀)ᵒᵖ ⥤
    (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u :=
  (fgIndexAboveInclusion T μ₀).op ⋙
    ((fgStageDiagram T ⋙ BigAffineFppf.inclusion B _ _) ⋙ yoneda)

/-- The cone with vertex `h_T` over the approximating system of presheaves. -/
noncomputable def yonedaStageCone : Cone (yonedaStageSystem T μ₀) :=
  (yoneda.mapCone ((BigAffineFppf.inclusion B _ _).mapCone (fgStageCone T))).whisker
    (fgIndexAboveInclusion T μ₀).op

/-- `h_T` is the limit of the approximating system of presheaves: the Yoneda embedding preserves
the limit `T = lim Spec R_μ`, and the subalgebras containing `μ₀` are cofinal. -/
noncomputable def isLimit_yonedaStageCone : IsLimit (yonedaStageCone T μ₀) :=
  (Functor.Initial.isLimitWhiskerEquiv (fgIndexAboveInclusion T μ₀).op _).symm
    (BigAffineFppf.isLimit_yoneda_mapCone B _ _ (isLimit_toScheme_mapCone_fgStageCone T))

/-- **The approximating system has bounded charts.** Its index is no larger than the power set of
`Γ(T)`, which is below the cutoff, the cutoff being a strong limit; and the base change of an
affine point `U₀ ⟶ Spec R_{μ}` along a transition `Spec R_ν ⟶ Spec R_μ` is no larger than the
larger of `U₀` and `T`. The index may well exceed the cofinality of the cutoff. -/
theorem chartsBounded_yonedaStageSystem :
    Space.ChartsBounded B (⊤_ Scheme.{u}) B.contains_terminal (yonedaStageSystem T μ₀) := by
  have hT : ((BigAffineFppf.toScheme B _ _).obj T).size < B.cutoff := T.obj.left.property
  have hI : #(FgIndexAbove T μ₀)ᵒᵖ < B.cutoff :=
    calc #(FgIndexAbove T μ₀)ᵒᵖ = #(FgIndexAbove T μ₀) :=
          mk_congr (Opposite.equivToOpposite (α := FgIndexAbove T μ₀)).symm
      _ ≤ #(FgIndex T) := mk_le_of_injective Subtype.val_injective
      _ ≤ #(Subalgebra ℤ (globalRing T)) := mk_le_of_injective Subtype.val_injective
      _ ≤ #(Set (globalRing T)) := mk_le_of_injective SetLike.coe_injective
      _ = 2 ^ #(globalRing T) := mk_set
      _ < B.cutoff := B.cutoff_isStrongPrelimit
        ((le_max_right _ _).trans_lt ((Scheme.size_of_isAffine _).symm.le.trans_lt hT))
  refine Space.chartsBounded_of_size_le B _ _ _ hI
    (fun i => mk_over_lt_of_mk_lt B.aleph0_lt_cutoff hI
      (fun _ _ => (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans
        Cardinal.one_le_aleph0) i) ?_
  intro i₀ U₀ f₀
  refine ⟨max ((BigAffineFppf.toScheme B _ _).obj T).size
      ((BigFppfOver.toScheme B _ _).obj ((BigAffineFppf.inclusion B _ _).obj U₀)).size,
    max_lt hT U₀.obj.left.property, fun j a W e => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, yoneda.map g = f₀ := ⟨yoneda.preimage f₀, yoneda.map_preimage f₀⟩
  let m := (BigAffineFppf.inclusion B _ _).map
    ((fgStageDiagram T).map ((fgIndexAboveInclusion T μ₀).op.map a))
  have hpb := (IsPullback.of_hasPullback m g).map yoneda
  let e' : W ≅ pullback m g := Yoneda.fullyFaithful.preimageIso (e ≪≫ hpb.isoPullback.symm)
  calc ((BigFppfOver.toScheme B _ _).obj W).size
      = ((BigFppfOver.toScheme B _ _).obj (pullback m g)).size :=
        Scheme.size_congr ((BigFppfOver.toScheme B _ _).mapIso e')
    _ ≤ _ := Space.size_pullback_le B _ _ m g
    _ ≤ _ := max_le_max (size_spec_fgIndex_le T j.unop.val) le_rfl

end AlgebraicGeometry.BigAffineFppf

namespace AlgebraicGeometry.Space

open BigAffineFppf

variable {B : BigFppfSite.{u}}

/-- **Noetherian approximation of a finitely presented, flat and proper algebraic space over an
affine base.** Let `T` be an affine object of the big fppf site of the terminal scheme and
`f : X ⟶ h_T` finitely presented, flat and proper. Then there are

* a directed set `I` (the finitely generated `ℤ`-subalgebras of `Γ(T)` containing a fixed one)
  and an inverse system `Tsys` of affine objects `T_i = Spec R_i` of the site, with `R_i`
  Noetherian, and a cone `tπ` exhibiting `T` as their limit;
* a descent situation `D` (Stacks 09RH) over `I` whose limiting cone is `(X, π)`, whose system has
  bounded charts (`AlgebraicGeometry.Space.ChartsBounded`, although `#I` may exceed the
  cofinality of the cutoff);
* finitely presented, flat and proper morphisms `fsys_i : X_i ⟶ h_{T_i}` from its stages, such
  that `X = X_i ×_{T_i} T` along `π_i` and `f`, and `X_j = X_i ×_{T_i} T_j` along the transition
  morphisms.

The family descends to a stage by `AlgebraicGeometry.properFlatFamilyDescendsAlongAffineLimit`
(Stacks 07SK, 0851, 08K1 and 08K0 over an affine limit), and the stages are its base changes
along the approximating system. -/
theorem exists_descentSituation_noetherianApproximation
    (T : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B _ _ X)
    (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B _ _).obj T))
    (hfp : IsFinitePresentation B _ _ f) (hfl : IsFlat B _ _ f) (hpr : IsProper B _ _ f) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (D : DescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal I)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D.system)
      (Tsys : Iᵒᵖ ⥤ BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal)
      (tπ : (Functor.const Iᵒᵖ).obj T ⟶ Tsys)
      (fsys : D.system ⟶ Tsys ⋙ BigAffineFppf.inclusion B _ _ ⋙ yoneda),
      D.limitCone = Cone.mk X π ∧
      ChartsBounded B _ _ D.system ∧
      Nonempty (IsLimit ((BigAffineFppf.toScheme B _ _).mapCone (Cone.mk T tπ))) ∧
      (∀ i : I, IsNoetherianRing Γ((BigAffineFppf.toScheme B _ _).obj (Tsys.obj (op i)), ⊤)) ∧
      (∀ i : I, IsFinitePresentation B _ _ (fsys.app (op i)) ∧
        IsFlat B _ _ (fsys.app (op i)) ∧ IsProper B _ _ (fsys.app (op i))) ∧
      (∀ i : I, IsPullback (π.app (op i)) f (fsys.app (op i))
        (yoneda.map ((BigAffineFppf.inclusion B _ _).map (tπ.app (op i))))) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsPullback (D.system.map a) (fsys.app i) (fsys.app j)
        (yoneda.map ((BigAffineFppf.inclusion B _ _).map (Tsys.map a)))) := by
  obtain ⟨i, Zi, hZi, fi, g, hfpi, hfli, hpri, hsq⟩ :=
    properFlatFamilyDescendsAlongAffineLimit B (⊤_ Scheme.{u}) B.contains_terminal
      (FgIndex T)ᵒᵖ (fgStageDiagram T) (fgStageCone T) (isLimit_toScheme_mapCone_fgStageCone T)
      X hX f hfp hfl hpr
  let μ₀ : FgIndex T := i.unop
  let Fi := fgIndexAboveInclusion T μ₀
  let G := (fgStageDiagram T ⋙ BigAffineFppf.inclusion B _ _) ⋙ yoneda
  let E := yonedaStageSystem T μ₀
  let Y := G.obj i
  have hstage (j : (FgIndex T)ᵒᵖ) :
      IsAffine ((BigFppfOver.toScheme B _ _).obj
        ((fgStageDiagram T ⋙ BigAffineFppf.inclusion B _ _).obj j)) :=
    ((fgStageDiagram T).obj j).property
  have hGalg (j) : IsAlgebraicSpace B _ _ (G.obj j) := isAlgebraicSpace_yoneda B _ _ _
  have hGqc (j) : IsQuasiCompactSpace B _ _ (G.obj j) :=
    isQuasiCompactSpace_yoneda_of_isAffine B _ _ _ (hstage j)
  have hGqs (j) : IsAbsolutelyQuasiSeparated B _ _ B.contains_terminal (G.obj j) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B _ _ B.contains_terminal _).mpr
      (by have := hstage j; infer_instance)
  have hGaff {j k : (FgIndex T)ᵒᵖ} (a : j ⟶ k) : IsAffineHom B _ _ (G.map a) :=
    have := hstage j
    have := hstage k
    isAffineHom_yoneda_map_of_isAffineHom _ inferInstance
  let t : E ⟶ (Functor.const (FgIndexAbove T μ₀)ᵒᵖ).obj Y :=
    { app j := G.map (homOfLE j.unop.2).op
      naturality j k a :=
        ((G.map_comp _ _).symm.trans (congrArg G.map (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  let sys := baseChangeOverSystem B _ _ E t fi
  let cE := yonedaStageCone T μ₀
  let gT : cE.pt ⟶ Y := (BigAffineFppf.inclusion B _ _ ⋙ yoneda).map ((fgStageCone T).π.app i)
  have hg (j) : cE.π.app j ≫ t.app j = gT :=
    ((BigAffineFppf.inclusion B _ _ ⋙ yoneda).map_comp _ _).symm.trans
      (congrArg (BigAffineFppf.inclusion B _ _ ⋙ yoneda).map ((fgStageCone T).w _))
  let bc := baseChangeOverCone B _ _ E t fi cE gT hg
  have hbc : IsLimit bc := isLimit_baseChangeOverCone B _ _ E t fi cE gT hg
    (isLimit_yonedaStageCone T μ₀)
  let e : X ≅ pullback gT fi := hsq.flip.isoPullback
  let π : (Functor.const (FgIndexAbove T μ₀)ᵒᵖ).obj X ⟶ sys :=
    (Functor.const _).map e.hom ≫ bc.π
  have hπ : IsLimit (Cone.mk X π) :=
    hbc.ofIsoLimit (Cones.ext e.symm fun j => (e.inv_hom_id_assoc _).symm)
  have hsysalg (j) : IsAlgebraicSpace B _ _ (sys.obj j) :=
    isAlgebraicSpace_pullback B _ _ (t.app j) fi (hGalg _) hZi (hGalg _)
  have hsq_j (j) : IsPullback (pullback.fst (t.app j) fi) (pullback.snd (t.app j) fi)
      (t.app j) fi := IsPullback.of_hasPullback _ _
  have hfpj (j) : IsFinitePresentation B _ _ (pullback.fst (t.app j) fi) :=
    IsFinitePresentation.of_isPullback B _ _ (hsysalg j) hZi (hGalg _) (hGalg _) (hsq_j j).flip
      hfpi
  have hflj (j) : IsFlat B _ _ (pullback.fst (t.app j) fi) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B _ _ (hsq_j j) hZi (hGalg _) hfli
  have hprj (j) : IsProper B _ _ (pullback.fst (t.app j) fi) :=
    isProper_pullback_fst B _ _ hZi (hGalg _) (hGalg _) fi (t.app j) hpri
  have htrans {j k : (FgIndexAbove T μ₀)ᵒᵖ} (a : j ⟶ k) :=
    isPullback_baseChangeOverMap B _ _ (t.app j) (t.app k) (E.map a) (by simp) fi
  let D : DescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
      (FgIndexAbove T μ₀) :=
    { system := sys
      algebraicSpace := fun j => hsysalg (op j)
      transition_affine := fun a => isAffineHom_of_isPullback (htrans a).flip (hGaff _)
      quasiCompact := fun j => isQuasiCompactSpace_of_isFinitePresentation B _ _ _ (hGalg _)
        (hGqc _) (hfpj (op j))
      quasiSeparated := fun j => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ _
        B.contains_terminal (hsysalg (op j)) (hGqs _) (hfpj (op j)).2.2
      limitCone := Cone.mk X π
      isLimit := hπ
      limitAlgebraicSpace := hX
      base := ⟨μ₀, le_rfl⟩ }
  refine ⟨FgIndexAbove T μ₀, inferInstance, inferInstance, D, π, Fi.op ⋙ fgStageDiagram T,
    Functor.whiskerLeft Fi.op (fgStageCone T).π, baseChangeOverProj B _ _ E t fi, rfl,
    ChartsBounded.baseChangeOver (chartsBounded_yonedaStageSystem T μ₀) t fi,
    ⟨IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv Fi.op _).symm
      (isLimit_toScheme_mapCone_fgStageCone T)) (Functor.mapConeWhisker _).symm⟩,
    fun j => isNoetherianRing_fgStage T j.val,
    fun j => ⟨hfpj (op j), hflj (op j), hprj (op j)⟩, fun j => ?_, fun a => htrans a⟩
  have hbcm := isPullback_baseChangeOverMap B _ _ gT (t.app (op j)) (cE.π.app (op j))
    (hg (op j)) fi
  refine IsPullback.of_iso_pullback ⟨?_⟩ (e ≪≫ hbcm.isoPullback) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hbcm.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hsq.flip.isoPullback_hom_fst)))
  · exact (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) hbcm.isoPullback_hom_fst)
  · exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hbcm.isoPullback_hom_snd).trans
      hsq.flip.isoPullback_hom_fst)

end AlgebraicGeometry.Space

end
