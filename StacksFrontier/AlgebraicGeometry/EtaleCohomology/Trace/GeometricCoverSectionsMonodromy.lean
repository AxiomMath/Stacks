module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricQuotientGaloisEquiv

/-!
# Sections of covers with trivial geometric monodromy, and the Galois action on them

Let `X` be a geometrically connected smooth curve over `k`, `k̄` an algebraically closed algebraic
extension, `η̄` a geometric point of `X_k̄` and `V` a finite étale cover of `X` on whose geometric
fibre at the image of `η̄` the geometric fundamental group `π₁(X_k̄, η̄)` acts trivially.

* Sections of a finite étale cover of a connected scheme whose fibre is fixed by the fundamental
  group are exactly its fibre points
  (`AlgebraicGeometry.bijective_finiteEtaleFiber_map_terminalCoverPoint`, Tag 0BND (1)).
* For an `X`-morphism `τ : X_k̄ ⟶ V` and `γ ∈ π₁(X, x̄)` with image `σ ∈ Aut(k̄/k)`, the point
  `τ ∘ (id × Spec σ)` of the fibre of `V` is `γ` applied to the point `τ`
  (`AlgebraicGeometry.fieldBaseChangeCoverPoint_galoisBaseChange`).

## Implementation notes

The second statement is proved with the monodromy `δ` of a path in `X_k̄` from `η̄` to its
translate (`AlgebraicGeometry.selfMapPathAut`), compared with `γ` on finite étale `k`-schemes
through `AlgebraicGeometry.geometricQuotientGaloisEquiv_spec`; `δ γ⁻¹` then comes from `π₁(X_k̄)`
by Tag 0BTX. The path is chosen inside the proof only.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Sections

variable {Y : Scheme.{u}} [ConnectedSpace Y] (y : GeometricPoint Y)

/-- The point of the geometric fibre of the terminal cover `Y ⟶ Y`. -/
def terminalCoverPoint : (finiteEtaleFiberFunctor y).obj (terminalCover Y) :=
  ⟨y.hom, Category.comp_id _⟩

/-- **Sections of a finite étale cover with trivial monodromy are its fibre points.** If every
element of `π₁(Y, y)` fixes every point of the geometric fibre of a finite étale cover `W` of a
connected scheme `Y`, then evaluating a section of `W` at `y` is a bijection from the sections of
`W` onto its geometric fibre. This is Tag 0BND (1): sections are the morphisms from the terminal
cover, whose fibre is a point, and the fibre functor is fully faithful into continuous
`π₁(Y, y)`-sets. -/
theorem bijective_finiteEtaleFiber_map_terminalCoverPoint (W : FiniteEtaleOver Y)
    (hW : ∀ (σ : EtaleFundamentalGroup Y y) (p : (finiteEtaleFiberFunctor y).obj W),
      (σ.app W).hom p = p) :
    Function.Bijective
      (fun t : terminalCover Y ⟶ W =>
        (finiteEtaleFiberFunctor y).map t (terminalCoverPoint y)) := by
  let eq := finiteEtaleEquivalenceOfIsGaloisCategory Y y
  refine ⟨fun t₁ t₂ h => ?_, fun p => ?_⟩
  · apply eq.functor.map_injective
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext a
    obtain rfl : a = terminalCoverPoint y :=
      Subsingleton.elim (α := (finiteEtaleFiberFunctor y).obj (terminalCover Y)) _ _
    exact h
  · let f : eq.functor.obj (terminalCover Y) ⟶ eq.functor.obj W :=
      ObjectProperty.homMk
        { hom := FintypeCat.homMk (fun _ => p)
          comm := fun g => by
            ext a
            exact (hW g p).symm.trans
              (finiteEtaleEquivalenceOfIsGaloisCategory_action Y y W g p).symm }
    exact ⟨eq.functor.preimage f,
      congrArg (fun φ : eq.functor.obj (terminalCover Y) ⟶ eq.functor.obj W =>
        φ.hom.hom (terminalCoverPoint y)) (eq.functor.map_preimage f)⟩

end Sections

section Path

variable {Y S : Scheme.{u}} [ConnectedSpace Y] [ConnectedSpace S] (pr : Y ⟶ S) (s : Y ⟶ Y)
  (hs : s ≫ pr = pr) (y : GeometricPoint Y)

/-- The geometric fibre functors of `S` at `(y.map s).map pr` and at `y.map pr` agree when
`s ≫ pr = pr`: the two geometric points have the same residue field and equal morphisms. -/
def finiteEtaleFiberFunctorMapSelfMapIso :
    finiteEtaleFiberFunctor ((y.map s).map pr) ≅ finiteEtaleFiberFunctor (y.map pr) :=
  NatIso.ofComponents (fun V ↦ Equiv.toIso (Equiv.subtypeEquivRight (fun f ↦ by
    change f ≫ V.hom = (y.hom ≫ s) ≫ pr ↔ f ≫ V.hom = y.hom ≫ pr
    rw [Category.assoc, hs])))
    (fun _ ↦ rfl)

variable (π : finiteEtaleFiberFunctor y ≅ finiteEtaleFiberFunctor (y.map s))

/-- **The monodromy of a path.** An isomorphism `π` of the geometric fibre functors of `Y` at `y`
and at `y.map s`, for an endomorphism `s` of `Y` over `S`, induces an automorphism of the geometric
fibre functor of `S` at the image of `y`: pull a finite étale cover of `S` back to `Y`, transport
along `π`, and project back. -/
def selfMapPathAut : EtaleFundamentalGroup S (y.map pr) :=
  (finiteEtaleFiberProjectionIso pr y).symm ≪≫
    Functor.isoWhiskerLeft (finiteEtaleBaseChange pr) π ≪≫
    finiteEtaleFiberProjectionIso pr (y.map s) ≪≫ finiteEtaleFiberFunctorMapSelfMapIso pr s hs y

omit [ConnectedSpace Y] in
/-- **The monodromy of a path on the point of a section.** For a section `t` of the pullback to
`Y` of a finite étale cover `V` of `S`, the automorphism `selfMapPathAut` carries the point of the
fibre of `V` given by `t` at `y` to the point given by `t` at `y.map s`. -/
theorem selfMapPathAut_app_section (V : FiniteEtaleOver S)
    (t : terminalCover Y ⟶ (finiteEtaleBaseChange pr).obj V) :
    (((selfMapPathAut pr s hs y π).app V).hom
        (finiteEtaleFiberProjection pr y V
          ((finiteEtaleFiberFunctor y).map t (terminalCoverPoint y)))).1 =
      y.hom ≫ s ≫ t.left ≫ pullback.fst V.hom pr := by
  have hπ := congrArg (fun φ => φ (terminalCoverPoint y)) (π.hom.naturality t)
  dsimp only [types_comp_apply] at hπ
  have hpt : π.hom.app (terminalCover Y) (terminalCoverPoint y) = terminalCoverPoint (y.map s) :=
    Subsingleton.elim (α := (finiteEtaleFiberFunctor (y.map s)).obj (terminalCover Y)) _ _
  rw [hpt] at hπ
  show ((finiteEtaleFiberProjectionEquiv pr (y.map s) V)
      (π.hom.app ((finiteEtaleBaseChange pr).obj V)
        ((finiteEtaleFiberProjectionEquiv pr y V).symm
          ((finiteEtaleFiberProjectionEquiv pr y V)
            ((finiteEtaleFiberFunctor y).map t (terminalCoverPoint y)))))).1 = _
  rw [Equiv.symm_apply_apply, hπ]
  show ((y.hom ≫ s) ≫ t.left) ≫ pullback.fst V.hom pr = _
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end Path

section Galois

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- The section `X_k̄ ⟶ X_k̄ ×_X V` of the pullback of a finite étale cover `V` of `X` given by an
`X`-morphism `τ : X_k̄ ⟶ V`. -/
def fieldBaseChangeCoverSection (V : FiniteEtaleOver X.1)
    (τ : fieldBaseChange (Over.mk f) kbar ⟶ V.left)
    (hτ : τ ≫ V.hom = fieldBaseChangeProj (Over.mk f) kbar) :
    terminalCover (fieldBaseChange (Over.mk f) kbar) ⟶
      (finiteEtaleBaseChange (fieldBaseChangeProj (Over.mk f) kbar)).obj V :=
  MorphismProperty.Over.homMk (pullback.lift τ (𝟙 _) (hτ.trans (Category.id_comp _).symm))
    (pullback.lift_snd _ _ _)

/-- The point of the geometric fibre of `V` at the image of `η̄` given by an `X`-morphism
`τ : X_k̄ ⟶ V` precomposed with an endomorphism `s` of `X_k̄` over `X`. -/
def fieldBaseChangeCoverPoint (V : FiniteEtaleOver X.1)
    (s : fieldBaseChange (Over.mk f) kbar ⟶ fieldBaseChange (Over.mk f) kbar)
    (hs : s ≫ fieldBaseChangeProj (Over.mk f) kbar = fieldBaseChangeProj (Over.mk f) kbar)
    (τ : fieldBaseChange (Over.mk f) kbar ⟶ V.left)
    (hτ : τ ≫ V.hom = fieldBaseChangeProj (Over.mk f) kbar) :
    finiteEtaleFiber (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) V :=
  ⟨y.hom ≫ s ≫ τ, by
    change (y.hom ≫ s ≫ τ) ≫ V.hom = y.hom ≫ fieldBaseChangeProj (Over.mk f) kbar
    rw [Category.assoc, Category.assoc, hτ, hs]⟩

omit [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar] in
/-- **The monodromy of a path on the point of an `X`-morphism.** For an endomorphism `s` of `X_k̄`
over `X` and an `X`-morphism `τ : X_k̄ ⟶ W`, the monodromy `selfMapPathAut` of a path from `η̄` to
its translate by `s` carries the point `τ` of the fibre of `W` to the point `τ ∘ s`. -/
theorem selfMapPathAut_app_fieldBaseChangeCoverPoint [ConnectedSpace X.1]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (s : fieldBaseChange (Over.mk f) kbar ⟶ fieldBaseChange (Over.mk f) kbar)
    (hs : s ≫ fieldBaseChangeProj (Over.mk f) kbar = fieldBaseChangeProj (Over.mk f) kbar)
    (π : finiteEtaleFiberFunctor y ≅ finiteEtaleFiberFunctor (y.map s))
    (W : FiniteEtaleOver X.1) (τ : fieldBaseChange (Over.mk f) kbar ⟶ W.left)
    (hτ : τ ≫ W.hom = fieldBaseChangeProj (Over.mk f) kbar) :
    ((selfMapPathAut (fieldBaseChangeProj (Over.mk f) kbar) s hs y π :
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)).app W).hom
        (fieldBaseChangeCoverPoint B X f kbar y W (𝟙 _) (Category.id_comp _) τ hτ) =
      fieldBaseChangeCoverPoint B X f kbar y W s hs τ hτ := by
  have h := selfMapPathAut_app_section (fieldBaseChangeProj (Over.mk f) kbar) s hs y π W
    (fieldBaseChangeCoverSection B X f kbar W τ hτ)
  have hp : finiteEtaleFiberProjection (fieldBaseChangeProj (Over.mk f) kbar) y W
      ((finiteEtaleFiberFunctor y).map (fieldBaseChangeCoverSection B X f kbar W τ hτ)
        (terminalCoverPoint y)) =
      fieldBaseChangeCoverPoint B X f kbar y W (𝟙 _) (Category.id_comp _) τ hτ :=
    Subtype.ext (by
      show (y.hom ≫ pullback.lift τ (𝟙 _) _) ≫ pullback.fst W.hom _ = y.hom ≫ 𝟙 _ ≫ τ
      exact (Category.assoc _ _ _).trans (congrArg (y.hom ≫ ·)
        ((pullback.lift_fst _ _ _).trans (Category.id_comp τ).symm)))
  rw [hp] at h
  refine Subtype.ext (h.trans ?_)
  show y.hom ≫ s ≫ pullback.lift τ (𝟙 _) _ ≫ pullback.fst W.hom _ = y.hom ≫ s ≫ τ
  exact congrArg (fun z => y.hom ≫ s ≫ z) (pullback.lift_fst _ _ _)

omit [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar] in
/-- A point `q` of the fibre of a finite étale `k`-scheme `Y` at the image of `η̄` which factors
through a `k̄`-point `e` of `Y` corresponds, in the fibre of the base change of `Y` to `X`, to the
point of the `X`-morphism `X_k̄ ⟶ X ×_k Y` induced by `e`. -/
theorem finiteEtaleFiberProjectionEquiv_symm_eq_fieldBaseChangeCoverPoint
    (Y : FiniteEtaleOver (Spec (.of k))) (e : Spec (.of kbar) ⟶ Y.left)
    (he : e ≫ Y.hom = specAlgebraMap k kbar)
    (q : finiteEtaleFiber ((y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f) Y)
    (hq : q.1 = geometricPointToSpec B X f kbar y ≫ e) :
    (finiteEtaleFiberProjectionEquiv f _ Y).symm q =
      fieldBaseChangeCoverPoint B X f kbar y ((finiteEtaleBaseChange f).obj Y) (𝟙 _)
        (Category.id_comp _)
        (pullback.lift (f := Y.hom) (g := f)
          (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar) ≫ e)
          (fieldBaseChangeProj (Over.mk f) kbar)
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) he).trans pullback.condition.symm)))
        (pullback.lift_snd _ _ _) := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · show pullback.lift q.1 _ _ ≫ pullback.fst Y.hom f =
      (y.hom ≫ 𝟙 _ ≫ _) ≫ pullback.fst Y.hom f
    refine (pullback.lift_fst _ _ _).trans (hq.trans ?_)
    show y.hom ≫ pullback.snd (Over.mk f).hom (specAlgebraMap k kbar) ≫ e = _
    rw [Category.id_comp, Category.assoc, pullback.lift_fst]
  · show pullback.lift q.1 _ _ ≫ pullback.snd Y.hom f =
      (y.hom ≫ 𝟙 _ ≫ _) ≫ pullback.snd Y.hom f
    rw [pullback.lift_snd, Category.id_comp, Category.assoc, pullback.lift_snd]
    rfl

/-- If an element `δ` of `π₁(X, x̄)` carries, for every `X`-morphism `τ : X_k̄ ⟶ W` to a finite
étale cover of `X`, the point `τ` to the point `τ ∘ (id × Spec σ)`, where `σ ∈ Aut(k̄/k)` is the
image of `γ ∈ π₁(X, x̄)`, then `δ` and `γ` have the same image in `π₁(Spec k, x̄)`. -/
theorem etaleFundamentalGroupMap_eq_of_app_fieldBaseChangeCoverPoint
    (γ δ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (hδ : ∀ (W : FiniteEtaleOver X.1) (τ : fieldBaseChange (Over.mk f) kbar ⟶ W.left)
      (hτ : τ ≫ W.hom = fieldBaseChangeProj (Over.mk f) kbar),
      (δ.app W).hom (fieldBaseChangeCoverPoint B X f kbar y W (𝟙 _) (Category.id_comp _) τ hτ) =
        fieldBaseChangeCoverPoint B X f kbar y W
          (galoisBaseChange (Over.mk f) kbar
            (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)))
          (galoisBaseChange_comp_fst _ _ _) τ hτ) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    etaleFundamentalGroupMap f (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) δ =
      etaleFundamentalGroupMap f (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) γ := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  set σ := geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)
  set s := galoisBaseChange (Over.mk f) kbar σ
  apply Iso.ext
  ext Y q
  let t := finiteEtaleFiberPrecompIso (geometricPointToSpec B X f kbar y)
    (x := algebraicClosureGeometricPoint k kbar)
    (x' := (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f)
    (geometricPointToSpec_comp_specAlgebraMap B X f kbar y)
  let e₀ := t.inv.app Y q
  have hq : q = t.hom.app Y e₀ :=
    (congrArg (fun φ => φ q) (congrArg (fun η => NatTrans.app η Y) t.inv_hom_id)).symm
  obtain ⟨e, he⟩ := e₀
  have hq' : q = t.hom.app Y ⟨e, he⟩ := hq
  have he' : e ≫ Y.hom = specAlgebraMap k kbar := he
  have hp : q.1 = geometricPointToSpec B X f kbar y ≫ e := by rw [hq']; rfl
  have hγ := geometricQuotientGaloisEquiv_spec B X f kbar y γ Y e he' q hp
  have hsymm := finiteEtaleFiberProjectionEquiv_symm_eq_fieldBaseChangeCoverPoint
    B X f kbar y Y e he' q hp
  refine Subtype.ext ?_
  change (finiteEtaleFiberProjection f _ Y ((δ.app ((finiteEtaleBaseChange f).obj Y)).hom
    ((finiteEtaleFiberProjectionEquiv f _ Y).symm q))).1 = _
  erw [hsymm, hδ _ _ (pullback.lift_snd _ _ _)]
  refine Eq.trans ?_ hγ.symm
  change (y.hom ≫ s ≫ _) ≫ pullback.fst Y.hom f = _
  rw [Category.assoc, Category.assoc, pullback.lift_fst]
  erw [← Category.assoc s, galoisBaseChange_comp_snd, Category.assoc, Category.assoc]

/-- **The Galois action on a section is the monodromy.** Let `V` be a finite étale cover of `X`
on whose geometric fibre at the image `x̄` of `η̄` the geometric fundamental group `π₁(X_k̄, η̄)`
acts trivially, and let `τ : X_k̄ ⟶ V` be a morphism over `X`. For `γ ∈ π₁(X, x̄)` with image
`σ ∈ Aut(k̄/k)` (`AlgebraicGeometry.geometricQuotientGaloisEquiv`), the point `τ ∘ (id × Spec σ)`
of the fibre is `γ` applied to the point `τ`.

The proof compares `γ` with the monodromy `δ` of a path in `X_k̄` from `η̄` to its translate by
`id × Spec σ` (`AlgebraicGeometry.selfMapPathAut`): `δ` carries the point `τ` to the point
`τ ∘ (id × Spec σ)`, because `τ` is a section; on finite étale `k`-schemes, all of whose points
come from `k̄`-points, `δ` therefore acts as `e ↦ e ∘ Spec σ`, which is how the image of `γ` acts
(`AlgebraicGeometry.geometricQuotientGaloisEquiv_spec`); so `δ γ⁻¹` lies in the kernel of
`π₁(X, x̄) ⟶ π₁(Spec k, x̄)`, which is the image of `π₁(X_k̄, η̄)` (Tag 0BTX), and acts trivially
on the fibre of `V`. -/
theorem fieldBaseChangeCoverPoint_galoisBaseChange
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (V : FiniteEtaleOver X.1)
    (hV : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ (g : EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)
        (p : finiteEtaleFiber (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) V),
        ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g).app V).hom p = p)
    (τ : fieldBaseChange (Over.mk f) kbar ⟶ V.left)
    (hτ : τ ≫ V.hom = fieldBaseChangeProj (Over.mk f) kbar) :
    letI := connectedSpace_of_isCurve B X f
    fieldBaseChangeCoverPoint B X f kbar y V
        (galoisBaseChange (Over.mk f) kbar
          (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)))
        (galoisBaseChange_comp_fst _ _ _) τ hτ =
      (γ.app V).hom
        (fieldBaseChangeCoverPoint B X f kbar y V (𝟙 _) (Category.id_comp _) τ hτ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  set σ := geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)
  set s := galoisBaseChange (Over.mk f) kbar σ
  have hs : s ≫ fieldBaseChangeProj (Over.mk f) kbar = fieldBaseChangeProj (Over.mk f) kbar :=
    galoisBaseChange_comp_fst _ _ _
  obtain ⟨π⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace
    (fieldBaseChange (Over.mk f) kbar) y (y.map s)
  let δ : EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) :=
    selfMapPathAut (fieldBaseChangeProj (Over.mk f) kbar) s hs y π
  have hδ : ∀ (W : FiniteEtaleOver X.1) (τ' : fieldBaseChange (Over.mk f) kbar ⟶ W.left)
      (hτ' : τ' ≫ W.hom = fieldBaseChangeProj (Over.mk f) kbar),
      (δ.app W).hom (fieldBaseChangeCoverPoint B X f kbar y W (𝟙 _) (Category.id_comp _) τ' hτ') =
        fieldBaseChangeCoverPoint B X f kbar y W s hs τ' hτ' :=
    selfMapPathAut_app_fieldBaseChangeCoverPoint B X f kbar y s hs π
  have : CompactSpace X.1 := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.1 := quasiSeparatedSpace_of_quasiSeparated f
  have hker := range_etaleFundamentalGroupMap_eq_ker_of_isPullback_isAlgClosed k kbar f
    (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
    (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) y
  have hmem : δ * γ⁻¹ ∈ (etaleFundamentalGroupMap f (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)).toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact (congrArg (· * _) (etaleFundamentalGroupMap_eq_of_app_fieldBaseChangeCoverPoint
      B X f kbar y γ δ hδ)).trans (mul_inv_cancel _)
  rw [← hker] at hmem
  obtain ⟨g, hg⟩ := hmem
  rw [← hδ V τ hτ, eq_mul_of_mul_inv_eq hg.symm]
  exact hV g _

end Galois

end AlgebraicGeometry

end
