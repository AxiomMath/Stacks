module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Noetherian approximation of a proper morphism together with a flat module

Let `f : X ⟶ Spec A` be proper and locally of finite presentation, and let `E` be a
quasi-coherent `𝒪_X`-module of finite presentation which is flat over `Spec A`. Then there are a
Noetherian ring `A₀` with a ring map `A₀ →+* A`, a proper morphism `f₀ : X₀ ⟶ Spec A₀` whose base
change to `Spec A` is `f`, and a coherent `𝒪_{X₀}`-module `E₀`, flat over `Spec A₀`, whose pullback
to `X` is `E`. This is the reduction to a Noetherian base used throughout the theory of
cohomology and base change; the output is in the form taken by
`exists_finiteProjectiveModel_homology_iso_functorial`, in the namespace
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections`.

## Main results

* `AlgebraicGeometry.exists_isProper_isFlatOver_model_of_isLimit`: for a cofiltered limit
  `c.pt = lim D` of quasi-compact quasi-separated schemes with affine transition morphisms, a
  proper morphism of finite presentation `f : X ⟶ c.pt` with a flat module of finite presentation
  `E` is the base change of a proper morphism `f₀ : X₀ ⟶ D.obj i` carrying a flat module of finite
  presentation `E₀` with `E ≅ g^* E₀`.
* `AlgebraicGeometry.exists_noetherian_model_of_isProper`: the case `c.pt = Spec A`, written as
  the limit of the spectra of the finitely generated `ℤ`-subalgebras of `A`, at whose Noetherian
  stages a finitely presented quasi-coherent module is coherent.

## Implementation notes

The proof is the standard one, Stacks 01ZA / 01ZM / 081F / 01ZR / 05LY, and the point is to
reconcile the stages at which the four descents land.

1. `AlgebraicGeometry.exists_isProper_finitePresentation_overPullbackObj_of_isLimit` (01ZM part
   (1) followed by 01ZQ and 081F) gives a stage `j` and a proper model `Xⱼ ⟶ D.obj j`.
2. The base changes of `Xⱼ` along the transition morphisms into `j`,
   `AlgebraicGeometry.Scheme.baseChangeDiagram`, form a cofiltered system indexed by `Over j`
   with affine transitions, whose limit is `Xⱼ ×_{D.obj j} c.pt ≅ X`; 01ZR
   (`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`)
   applied to the cone over it with vertex `X` descends `E` to a module `F` on one of those base
   changes `Z = Xⱼ ×_{D.obj j} D.obj k`, which is proper over `D.obj k`.
3. 05LY (`AlgebraicGeometry.eventually_isFlatOver_modulePullback`) applied to `Z ⟶ D.obj k`
   makes the pullback of `F` flat over a later stage `D.obj l`. The hypothesis it needs, flatness
   at the limit, is the flatness of `E`, transported along the cartesian square
   (`AlgebraicGeometry.isFlatOver_pullback_fst_of_isPullback`).
4. The model is `X₀ = Z ×_{D.obj k} D.obj l`, and everything else is pasting of cartesian
   squares and the pseudofunctoriality of the pullback of modules.

Only the last step uses that the stages are Noetherian: there, a quasi-coherent module of finite
type is coherent (Stacks 01XZ).

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness of a module over the base of a cartesian square, read on the canonical pullback:
if `E` on `X` is flat over `S` and `E ≅ b^* F` for the top arrow `b : X ⟶ Z` of a cartesian
square, then the pullback of `F` to `Z ×_T S` is flat over `S`. -/
theorem isFlatOver_pullback_fst_of_isPullback {X Z S T : Scheme.{u}} {b : X ⟶ Z} {f : X ⟶ S}
    {q : Z ⟶ T} {π : S ⟶ T} (h : IsPullback b f q π) (F : Z.Modules) (E : X.Modules)
    [E.IsQuasicoherent] (eE : E ≅ (Scheme.Modules.pullback b).obj F)
    (hflat : IsFlatOver f.toLRSHom.toShHom E) :
    IsFlatOver (pullback.snd q π).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst q π)).obj F) := by
  let χ := h.isoPullback
  have hsq : IsPullback χ.inv (pullback.snd q π) f (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact h.isoPullback_inv_snd⟩
  have h₁ := @modulePullback_isFlatOver _ _ _ _ _ _ _ _ hsq E (isQuasicoherent_ringSheaf E) hflat
  refine isFlatOver_of_moduleIso _ ?_ h₁
  exact (Scheme.Modules.pullback χ.inv).mapIso eE ≪≫
    (Scheme.Modules.pullbackComp χ.inv b).app F ≪≫
    (Scheme.Modules.pullbackCongr h.isoPullback_inv_fst).app F

/-! ### Descending a proper morphism with a flat module to a stage of a limit -/

/-- An isomorphism of `Over.mk f` with the base change of `Y` along `π` exhibits `f` as a base
change of `Y.hom` along `π`. -/
private theorem isPullback_of_iso_overPullbackObj {X S T : Scheme.{u}} {f : X ⟶ S} {π : S ⟶ T}
    {Y : Over T} (e : Over.mk f ≅ (Over.pullback π).obj Y) :
    IsPullback (e.hom.left ≫ pullback.fst Y.hom π) f Y.hom π := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h₁ : IsPullback e.hom.left f (pullback.snd Y.hom π) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩
  simpa only [Category.id_comp] using h₁.paste_horiz (IsPullback.of_hasPullback Y.hom π)

/-- If `X` is the base change of `Xj.hom` along `c.π.app j`, then it is also the base change of
the stage `Xj ×_{D.obj j} D.obj k` of `AlgebraicGeometry.Scheme.baseChangeDiagram` along
`c.π.app k.left`, via the leg of `AlgebraicGeometry.Scheme.baseChangeCone`. -/
private theorem isPullback_baseChangeCone_π {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (j : I)
    (Xj : Over (D.obj j)) (c : Cone D) {X : Scheme.{u}} {g : X ⟶ Xj.left} {f : X ⟶ c.pt}
    (hsq : IsPullback g f Xj.hom (c.π.app j)) (k : Over j) :
    IsPullback ((hsq.flip.isoPullback.hom : X ⟶ (Scheme.baseChangeCone D j Xj c).pt) ≫
        (Scheme.baseChangeCone D j Xj c).π.app k : X ⟶ pullback (D.map k.hom) Xj.hom)
      f (pullback.fst (D.map k.hom) Xj.hom) (c.π.app k.left) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map k.hom) Xj.hom)
    (h₂₂ := D.map k.hom) ?_ ?_ (IsPullback.of_hasPullback (D.map k.hom) Xj.hom).flip
  · erw [Category.assoc, Scheme.baseChangeCone_π_snd, hsq.flip.isoPullback_hom_snd, c.w k.hom]
    exact hsq
  · erw [Category.assoc, Scheme.baseChangeCone_π_fst, hsq.flip.isoPullback_hom_fst_assoc]

/-- **Flatness of a descended module at a later stage.** Let `c.pt = lim D` be as in
`AlgebraicGeometry.exists_isProper_isFlatOver_model_of_isLimit`, `q : Z ⟶ D.obj i` proper of
finite presentation with `X` its base change along `c.π.app i`, and `F` a module of finite
presentation on `Z` with `E ≅ b^* F` flat over `c.pt`. Then at a later stage `l` the base change
of `q` carries a flat module of finite presentation whose pullback to `X` is `E`. -/
private theorem exists_isProper_isFlatOver_model_of_isPullback {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) {X Z : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {b : X ⟶ Z}
    {q : Z ⟶ D.obj i} [hqprop : IsProper q] (hqfp : FinitePresentation q)
    (hbq : IsPullback b f q (c.π.app i)) (F : Z.Modules) (hF : F.IsFinitePresentation)
    (E : X.Modules) [E.IsQuasicoherent] (eE : E ≅ (Scheme.Modules.pullback b).obj F)
    (hflat : IsFlatOver f.toLRSHom.toShHom E) :
    ∃ (l : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj l) (g : X ⟶ X₀) (E₀ : X₀.Modules),
      IsProper f₀ ∧ IsPullback g f f₀ (c.π.app l) ∧ E₀.IsFinitePresentation ∧
        IsFlatOver f₀.toLRSHom.toShHom E₀ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback g).obj E₀) := by
  classical
  let Xk : Over (D.obj i) := Over.mk q
  have hlim : IsFlatOver ((Over.pullback (c.π.app i)).map
      (Over.homMk Xk.hom : Xk ⟶ Over.mk (𝟙 (D.obj i)))).left.toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst Xk.hom (c.π.app i))).obj F) := by
    refine (isFlatOver_overPullback_map_iff Xk (c.π.app i) _).mpr ?_
    exact isFlatOver_pullback_fst_of_isPullback hbq F E eE hflat
  have hFqc := Stacks.Modules.isQuasicoherent_of_isFinitePresentation F
  have hFqc' : SheafOfModules.IsQuasicoherent
      (R := structureSheafRing Xk.left.toRingedSpace) F := isQuasicoherent_ringSheaf F
  have hFfp' : SheafOfModules.IsFinitePresentation
      (R := structureSheafRing Xk.left.toRingedSpace) F := hF
  have hidfp : FinitePresentation (Over.mk (𝟙 (D.obj i))).hom :=
    (⟨inferInstance, inferInstance, inferInstance⟩ : FinitePresentation (𝟙 (D.obj i)))
  obtain ⟨l, e', hl⟩ := eventually_isFlatOver_modulePullback D c hc i Xk
    (Over.mk (𝟙 (D.obj i))) hqfp hidfp (Over.homMk Xk.hom) F hlim
  replace hl := (isFlatOver_overPullback_map_iff Xk (D.map e') _).mp hl
  have t := IsPullback.of_hasPullback q (D.map e')
  have hbq' : IsPullback b f q (c.π.app l ≫ D.map e') := by rwa [c.w e']
  refine ⟨l, pullback q (D.map e'), pullback.snd q (D.map e'),
    t.lift b (f ≫ c.π.app l) (by rw [hbq'.w, Category.assoc]),
    (Scheme.Modules.pullback (pullback.fst q (D.map e'))).obj F,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback t hqprop,
    IsPullback.of_right' hbq' t, Stacks.Modules.isFinitePresentation_pullback _ _ hF, hl, ⟨?_⟩⟩
  exact eE ≪≫ (Scheme.Modules.pullbackCongr (t.lift_fst _ _ _).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp _ _).app F).symm

/-- **A proper morphism with a flat module of finite presentation descends to a finite stage.**
Let `c.pt = lim D` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms, `f : X ⟶ c.pt` proper and locally of finite presentation, and `E` a
quasi-coherent `𝒪_X`-module of finite presentation flat over `c.pt`. Then there are a stage `i`, a
proper morphism `f₀ : X₀ ⟶ D.obj i` with a cartesian square `g, f, f₀, c.π.app i`, and a module
`E₀` of finite presentation on `X₀`, flat over `D.obj i`, with `E ≅ g^* E₀`. -/
theorem exists_isProper_isFlatOver_model_of_isLimit {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}}
    (f : X ⟶ c.pt) [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsQuasicoherent] [E.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom E) :
    ∃ (i : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj i) (g : X ⟶ X₀) (E₀ : X₀.Modules),
      IsProper f₀ ∧ IsPullback g f f₀ (c.π.app i) ∧ E₀.IsFinitePresentation ∧
        IsFlatOver f₀.toLRSHom.toShHom E₀ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback g).obj E₀) := by
  classical
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let Xo : Over c.pt := Over.mk f
  have : IsProper Xo.hom := ‹IsProper f›
  obtain ⟨j, Xj, hXjfp, hXjprop, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc Xo hfp
  -- the model `Xj.hom` and the cartesian square exhibiting `X` as its base change
  let g : X ⟶ Xj.left := e.hom.left ≫ pullback.fst Xj.hom (c.π.app j)
  have hsq : IsPullback g f Xj.hom (c.π.app j) := isPullback_of_iso_overPullbackObj e
  -- the system of base changes of `Xj.hom`, with limit `X`
  let τ : X ≅ pullback (c.π.app j) Xj.hom := hsq.flip.isoPullback
  let D' := Scheme.baseChangeDiagram D j Xj
  let τ₂ : X ⟶ (Scheme.baseChangeCone D j Xj c).pt := τ.hom
  have : IsIso τ₂ := inferInstanceAs (IsIso τ.hom)
  let c' : Cone D' := (Scheme.baseChangeCone D j Xj c).extend τ₂
  have hc' : IsLimit c' :=
    IsLimit.ofIsoLimit (Scheme.isLimitBaseChangeCone D j Xj c hc)
      (Cone.extendIso (Scheme.baseChangeCone D j Xj c) (asIso τ₂).symm)
  have hpb : ∀ k : Over j, IsPullback (pullback.snd (D.map k.hom) Xj.hom)
      (pullback.fst (D.map k.hom) Xj.hom) Xj.hom (D.map k.hom) := fun k =>
    (IsPullback.of_hasPullback (D.map k.hom) Xj.hom).flip
  have hD'aff : ∀ {k l : Over j} (a : k ⟶ l), IsAffineHom (D'.map a) := fun a =>
    Scheme.isAffineHom_baseChangeDiagram_map D j Xj a
  have hD'qc : ∀ k : Over j, CompactSpace (D'.obj k) := by
    intro k
    have : QuasiCompact (pullback.fst (D.map k.hom) Xj.hom) :=
      MorphismProperty.of_isPullback (hpb k) hXjfp.2.1
    exact (QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map k.hom) Xj.hom) :
      CompactSpace (pullback (D.map k.hom) Xj.hom : Scheme.{u}))
  have hD'qs : ∀ k : Over j, QuasiSeparatedSpace (D'.obj k) := by
    intro k
    have : QuasiSeparated (pullback.fst (D.map k.hom) Xj.hom) :=
      MorphismProperty.of_isPullback (hpb k) hXjfp.2.2
    exact (quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map k.hom) Xj.hom) :
      QuasiSeparatedSpace (pullback (D.map k.hom) Xj.hom : Scheme.{u}))
  -- descend the module to a stage `k` of the system of base changes
  obtain ⟨k, Fk, hFk, ⟨eE₀⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      D' c' hc' E
  let q : pullback (D.map k.hom) Xj.hom ⟶ D.obj k.left := pullback.fst (D.map k.hom) Xj.hom
  let b : X ⟶ pullback (D.map k.hom) Xj.hom := τ₂ ≫ (Scheme.baseChangeCone D j Xj c).π.app k
  have hqprop : IsProper q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb k) hXjprop
  have hbq : IsPullback b f q (c.π.app k.left) := isPullback_baseChangeCone_π D j Xj c hsq k
  exact exists_isProper_isFlatOver_model_of_isPullback D c hc
    (FinitePresentation.of_isPullback (hpb k) hXjfp) hbq Fk hFk E eE₀ hflat

/-! ### Noetherian approximation over an affine base -/

/-- **Absolute Noetherian approximation of a proper morphism to an affine scheme together with a
flat module.** Let `f : X ⟶ Spec A` be proper and locally of finite presentation and `E` a
quasi-coherent `𝒪_X`-module of finite presentation flat over `Spec A`. Then there are a Noetherian
ring `A₀`, a ring map `φ : A₀ →+* A`, a proper morphism `f₀ : X₀ ⟶ Spec A₀` with `X` its base
change along `Spec φ` (via `g : X ⟶ X₀`), and a coherent `𝒪_{X₀}`-module `E₀`, flat over
`Spec A₀`, with `E ≅ g^* E₀`.

`A₀` is the subring of `A` generated by a finite subset: `Spec A` is the limit of the spectra of
those subrings (`AlgebraicGeometry.isLimit_specAdjoinFinsetCone`), each of which is Noetherian,
and `AlgebraicGeometry.exists_isProper_isFlatOver_model_of_isLimit` applies. -/
@[ega "IV 11.2.7" "special case",
  ega "IV 8.1.2" "special case",
  ega "IV 8.9.1" "(i), special case",
  sga "1 VIII 3.6" "(ii) ⇒ (i), proper case"]
theorem exists_noetherian_model_of_isProper {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsQuasicoherent] [E.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom E) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : IsNoetherianRing A₀) (φ : A₀ →+* A)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of A₀)) (g : X ⟶ X₀) (E₀ : X₀.Modules),
      IsProper f₀ ∧ IsPullback g f f₀ (Spec.map (CommRingCat.ofHom φ)) ∧ E₀.IsCoherent ∧
        IsFlatOver f₀.toLRSHom.toShHom E₀ ∧
        Nonempty (E ≅ (Scheme.Modules.pullback g).obj E₀) := by
  let f' : X ⟶ (specAdjoinFinsetCone A).pt := f
  have : IsProper f' := ‹IsProper f›
  have : LocallyOfFinitePresentation f' := ‹LocallyOfFinitePresentation f›
  obtain ⟨i, X₀, f₀, g, E₀, hprop, hsq, hfp, hfl, ⟨eE⟩⟩ :=
    exists_isProper_isFlatOver_model_of_isLimit (specAdjoinFinsetDiagram A)
      (specAdjoinFinsetCone A) (isLimit_specAdjoinFinsetCone A) f' E hflat
  have : LocallyOfFiniteType f₀ := inferInstance
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      E₀ hfp
  refine ⟨Algebra.adjoin ℤ ((i.unop : Finset A) : Set A), inferInstance,
    isNoetherianRing_adjoinFinset_int A i.unop,
    (Algebra.adjoin ℤ ((i.unop : Finset A) : Set A)).val.toRingHom, X₀, f₀, g, E₀, hprop, hsq,
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
      E₀, hfl, ⟨eE⟩⟩

end AlgebraicGeometry
