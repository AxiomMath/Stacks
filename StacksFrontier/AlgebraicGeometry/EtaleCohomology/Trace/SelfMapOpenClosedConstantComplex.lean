module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapOpenClosedGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistIsoTransferTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralTwistedFrobeniusTrace

/-!
# Step 9 for a complex of constant sheaves: the twisted trace on `j_! j^{-1}` vanishes

Let `Y` be a scheme over a finite field `k`, `σ : Y ⟶ Y` a morphism over `k`, `j_V : V ⟶ Y` a
`σ`-stable open immersion with closed complement `W`, and `N` a bounded below complex of
`Λ`-modules. The complex `M = j_{V!} j_V^{-1} N_Y` of extensions by zero of constant sheaves
carries the maps `ε : M^n ⟶ σ_* M^n` (extension by zero of the canonical maps
`N^n_Y ⟶ σ_* N^n_Y`), whence the twisted Frobenius `(σ̄ π̄)^*` on `RΓ(Y_k̄, M|_{Y_k̄})`. Through
the identification `M|_{Y_k̄} ≅ j'_! j'^{-1} f^{-1} N_{k̄}` (`f : Y_k̄ ⟶ Spec k̄`) this is the
self-map twist of `φ = σ̄ π̄` restricted to the open `V_k̄`, so Step 9 applies: if `φ` has no fixed
`k̄`-point on `V_k̄`, `W_k̄` is finite étale over `k̄` and Weil's formula holds on `Y_k̄`, then the
trace vanishes. This is the glue between Step 8 (the twisted Frobenius of a cover) and Step 9 of
the proof of [Stacks, Tag 03UG].

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroConstantTwist`: the maps `ε`.
* `Stacks.EtaleCohomology.fieldBaseChangeExtensionByZeroConstantComplexIso`: the identification
  of complexes.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_zero`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u r

namespace CategoryTheory.Functor

section TwistedBaseChangeComponents

variable {A C' : Type*} [Category* A] [Category* C'] [Abelian A] [Abelian C']
  (P' : C' ⥤ C') (g' : A ⥤ C') (PZ : C' ⥤ C') (Sg : C' ⥤ C') (S : A ⥤ A)
  [P'.Additive] [g'.Additive] [S.Additive]
  (tw' : g' ⟶ g' ⋙ PZ) (aBC : S ⋙ g' ⟶ g' ⋙ Sg) (c : Sg ⋙ PZ ≅ P')

/-- The components of `CategoryTheory.Functor.twistedBaseChangeTwistHC`. -/
lemma twistedBaseChangeTwistHC_f (M : CochainComplex A ℤ) (ε : ∀ n, M.X n ⟶ S.obj (M.X n))
    (hε : ∀ i j, M.d i j ≫ ε j = ε i ≫ S.map (M.d i j)) (n : ℤ) :
    (twistedBaseChangeTwistHC P' g' PZ Sg S tw' aBC c M ε hε).f n =
      twistedBaseChangeTwist P' g' PZ Sg S tw' aBC c (M.X n) (ε n) := rfl

end TwistedBaseChangeComponents

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Naturality

variable (Λ : Type r) [Ring Λ]

/-- **The canonical map `M_X ⟶ s_* M_X` is natural in the module `M`.** -/
lemma constantSelfMapTwist_naturality {X : Scheme.{u}} (s : X ⟶ X)
    {M M' : ModuleCat.{max (u + 1) r} Λ} (x : M ⟶ M') :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map x ≫
        constantSelfMapTwist Λ M' s =
      constantSelfMapTwist Λ M s ≫ (etaleModuleDirectImage.{u, r} Λ s).map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map x) := by
  simp only [constantSelfMapTwist]
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  exact (etaleModuleInverseImageConstantIso.{u, r} Λ s).hom.naturality x

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- **The identification of the two pulled back constant sheaves is natural in the module.** -/
lemma fieldBaseChangeConstantIso_hom_naturality {M M' : ModuleCat.{max (u + 1) r} Λ} (x : M ⟶ M') :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map
        ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map x) ≫
      (fieldBaseChangeConstantIso Λ M' Y kbar).hom =
    (fieldBaseChangeConstantIso Λ M Y kbar).hom ≫
      (etaleModuleInverseImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
        ((constantSheaf (Spec (.of kbar)).smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ)).map x) := by
  have h₁ := (etaleModuleInverseImageConstantIso.{u, r} Λ
    (fieldBaseChangeProj Y kbar)).hom.naturality x
  have h₂ := (etaleModuleInverseImageConstantIso.{u, r} Λ
    (pullback.snd Y.hom (specAlgebraMap k kbar))).inv.naturality x
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [fieldBaseChangeConstantIso, inverseImageEtaleModuleConstantSheafIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% h₁, h₂, Category.assoc]

end Naturality

section OpenFix

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {V W : Scheme.{u}} (jV : V ⟶ Y.left) [IsOpenImmersion jV] (iW : W ⟶ Y.left) [IsClosedImmersion iW]
  (hij : Set.range jV.base = (Set.range iW.base)ᶜ) (σV : V ⟶ V) [IsIntegralHom σ.left]
  (sq : IsPullback σV jV jV σ.left)
  {V' W' : Scheme.{u}} (j' : V' ⟶ fieldBaseChange Y kbar) [IsOpenImmersion j']
  (i' : W' ⟶ fieldBaseChange Y kbar) [IsClosedImmersion i']
  (hij' : Set.range j'.base = (Set.range i'.base)ᶜ)
  (gW : W' ⟶ W) (hW : i' ≫ fieldBaseChangeProj Y kbar = gW ≫ iW)
  (gV : V' ⟶ V) (hV : j' ≫ fieldBaseChangeProj Y kbar = gV ≫ jV)

include hij' in
/-- **The identification of `(j_! j^{-1} M_Y)|_{Y_k̄}` with `j'_! j'^{-1} f^{-1} M_{k̄}` is natural
in the module `M`**: both are subobjects of `f^{-1} M_{k̄}` through the counits. -/
lemma fieldBaseChangeExtensionByZeroConstantIso_hom_naturality {M M' : ModuleCat.{u + 1} Λ}
    (x : M ⟶ M') :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jV).map ((etaleModuleRestriction.{u, 0} Λ jV).map
          ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x))) ≫
      (fieldBaseChangeExtensionByZeroConstantIso Λ M' Y kbar jV iW hij j' i' hij' gW hW gV hV).hom =
    (fieldBaseChangeExtensionByZeroConstantIso Λ M Y kbar jV iW hij j' i' hij' gW hW gV hV).hom ≫
      (etaleModuleExtensionByZero.{u, 0} Λ j').map ((etaleModuleRestriction.{u, 0} Λ j').map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x))) := by
  have hS := (shortExact_etaleModuleExtensionByZero_directImage.{u, 0} Λ i' j' hij'
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
      (etaleModuleConstantSheaf Λ M' (Spec (.of kbar))))).choose_spec
  have := hS.mono_f
  rw [← cancel_mono ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
      (etaleModuleConstantSheaf Λ M' (Spec (.of kbar)))))]
  have hcV := (etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).counit.naturality
    ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x)
  have hc' := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.naturality
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
      ((constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hcV hc'
  rw [Category.assoc, fieldBaseChangeExtensionByZeroConstantIso_hom_comp_counit, Category.assoc,
    hc', reassoc_of% (fieldBaseChangeExtensionByZeroConstantIso_hom_comp_counit Λ M Y kbar jV iW
      hij j' i' hij' gW hW gV hV), ← Functor.map_comp_assoc, hcV, Functor.map_comp_assoc,
    fieldBaseChangeConstantIso_hom_naturality]

variable (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

/-- The complex `j_{V!} j_V^{-1} N_Y` of extensions by zero of constant sheaves on `Y`. -/
abbrev extensionByZeroConstantComplex : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left) :=
  (etaleModuleExtensionByZero.{u, 0} Λ jV).mapCochainComplexPlus.obj
    ((etaleModuleRestriction.{u, 0} Λ jV).mapCochainComplexPlus.obj
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj N))

/-- The complex `N_{k̄}` of constant sheaves on `Spec k̄`. -/
abbrev etaleModuleConstantComplex : CochainComplex.Plus (EtaleModules.{u, 0} Λ (Spec (.of kbar))) :=
  (constantSheaf (Spec (.of kbar)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj N

/-- **The maps `ε : M^n ⟶ σ_* M^n`** on `M = j_{V!} j_V^{-1} N_Y`: the extensions by zero of the
canonical maps `N^n_Y ⟶ σ_* N^n_Y`. -/
abbrev extensionByZeroConstantTwist (n : ℤ) :
    (extensionByZeroConstantComplex Λ Y jV N).obj.X n ⟶
      (etaleModuleDirectImage.{u, 0} Λ σ.left).obj
        ((extensionByZeroConstantComplex Λ Y jV N).obj.X n) :=
  extensionByZeroTwist Λ jV σV σ.left sq (etaleModuleConstantSheaf Λ (N.obj.X n) Y.left)
    (constantSelfMapTwist Λ (N.obj.X n) σ.left)

/-- The maps `ε` commute with the differentials. -/
lemma extensionByZeroConstantTwist_comm (a b : ℤ) :
    (extensionByZeroConstantComplex Λ Y jV N).obj.d a b ≫
        extensionByZeroConstantTwist Λ Y σ jV σV sq N b =
      extensionByZeroConstantTwist Λ Y σ jV σV sq N a ≫
        (etaleModuleDirectImage.{u, 0} Λ σ.left).map
          ((extensionByZeroConstantComplex Λ Y jV N).obj.d a b) :=
  extensionByZeroTwist_naturality Λ jV σV σ.left sq _ _ _
    (constantSelfMapTwist_naturality Λ σ.left (N.obj.d a b))

/-- **The identification `(j_{V!} j_V^{-1} N_Y)|_{Y_k̄} ≅ j'_! j'^{-1} f^{-1} N_{k̄}`** of bounded
below complexes on `Y_k̄`. -/
def fieldBaseChangeExtensionByZeroConstantComplexIso :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        (extensionByZeroConstantComplex Λ Y jV N) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ j').mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
              (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
            (etaleModuleConstantComplex Λ kbar N))) :=
  ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
    (fun n => fieldBaseChangeExtensionByZeroConstantIso Λ (N.obj.X n) Y kbar jV iW hij j' i' hij'
      gW hW gV hV)
    (fun a b _ => (fieldBaseChangeExtensionByZeroConstantIso_hom_naturality Λ Y kbar jV iW hij j' i'
      hij' gW hW gV hV (N.obj.d a b)).symm))

/-- The components of the identification of complexes. -/
lemma fieldBaseChangeExtensionByZeroConstantComplexIso_hom_hom_f (n : ℤ) :
    (fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij' gW hW gV hV
      N).hom.hom.f n =
    (fieldBaseChangeExtensionByZeroConstantIso Λ (N.obj.X n) Y kbar jV iW hij j' i' hij' gW hW gV
      hV).hom := rfl

/-- The components of the inverse identification of complexes. -/
lemma fieldBaseChangeExtensionByZeroConstantComplexIso_inv_hom_f (n : ℤ) :
    (fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij' gW hW gV hV
      N).inv.hom.f n =
    (fieldBaseChangeExtensionByZeroConstantIso Λ (N.obj.X n) Y kbar jV iW hij j' i' hij' gW hW gV
      hV).inv := rfl

/-! ### The twist of the first term of the open/closed sequence -/

/-- The twist `Functor.twistedBaseChangeTwist` of the Frobenius data is the twisted Frobenius
twist. -/
lemma twistedBaseChangeTwist_eq_twistedFrobeniusTwist (C : EtaleModules.{u, 0} Λ Y.left)
    (ε : C ⟶ (etaleModuleDirectImage.{u, 0} Λ σ.left).obj C) :
    Functor.twistedBaseChangeTwist
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap σ kbar))
        (etaleModuleDirectImage.{u, 0} Λ σ.left)
        (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
        (automorphismBaseChange Λ Y σ kbar)
        (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap σ kbar)
          (geometricFrobeniusBaseChange Y kbar p q hcard)
          (twistedGeometricFrobenius Y σ kbar p q hcard) rfl) C ε =
      twistedFrobeniusTwist.{u, 0} Λ Y σ kbar p q hcard C ε := rfl


/-- The twisted Frobenius twist of `(j_{V!} j_V^{-1} N_Y)|_{Y_k̄}` attached to the maps `ε`. -/
abbrev extensionByZeroConstantTwistedFrobeniusHC :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex _).obj
        (extensionByZeroConstantComplex Λ Y jV N).obj ⟶
      ((etaleModuleDirectImage.{u, 0} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex
          _).obj (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
            _).obj (extensionByZeroConstantComplex Λ Y jV N).obj) :=
  Functor.twistedBaseChangeTwistHC
    (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap σ kbar))
    (etaleModuleDirectImage.{u, 0} Λ σ.left)
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
    (automorphismBaseChange Λ Y σ kbar)
    (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap σ kbar)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (twistedGeometricFrobenius Y σ kbar p q hcard) rfl)
    (extensionByZeroConstantComplex Λ Y jV N).obj
    (extensionByZeroConstantTwist Λ Y σ jV σV sq N)
    (extensionByZeroConstantTwist_comm Λ Y σ jV σV sq N)

/-- The components of the twisted Frobenius twist are twisted Frobenius twists of sheaves. -/
lemma extensionByZeroConstantTwistedFrobeniusHC_f (n : ℤ) :
    (extensionByZeroConstantTwistedFrobeniusHC Λ Y σ kbar p q hcard jV σV sq N).f n =
      twistedFrobeniusTwist.{u, 0} Λ Y σ kbar p q hcard _
        (extensionByZeroTwist Λ jV σV σ.left sq (etaleModuleConstantSheaf Λ (N.obj.X n) Y.left)
          (constantSelfMapTwist Λ (N.obj.X n) σ.left)) :=
  (Functor.twistedBaseChangeTwistHC_f _ _ _ _ _ _ _ _ _ _ _ n).trans
    (twistedBaseChangeTwist_eq_twistedFrobeniusTwist Λ Y σ kbar p q hcard _ _)

/-- **The twist `τ₁` of `j'_! j'^{-1} f^{-1} N_{k̄}`**: the twisted Frobenius twist transported
along `Stacks.EtaleCohomology.fieldBaseChangeExtensionByZeroConstantComplexIso`. -/
def extensionByZeroConstantOpenTwist :
    ((etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ j').mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
            (etaleModuleConstantComplex Λ kbar N)))).obj ⟶
      ((etaleModuleDirectImage.{u, 0} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex
          _).obj ((etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ j').mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
            (etaleModuleConstantComplex Λ kbar N)))).obj :=
  (fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij' gW hW gV hV
    N).inv.hom ≫
    extensionByZeroConstantTwistedFrobeniusHC Λ Y σ kbar p q hcard jV σV sq N ≫
      ((etaleModuleDirectImage.{u, 0} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex
        _).map (fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij'
          gW hW gV hV N).hom.hom

variable (fW : W' ⟶ Spec (.of kbar))
  (hfW : fW = i' ≫ pullback.snd Y.hom (specAlgebraMap k kbar))

/-- A componentwise criterion for `(e' ≫ t ≫ P(e)) ≫ P(s) = s ≫ m` for maps of complexes. -/
private lemma comp_mapHomologicalComplex_map_eq_of_f {C : Type*} [Category* C] [Preadditive C]
    (P : C ⥤ C) [P.Additive] {X A Z : CochainComplex C ℤ}
    (e' : X ⟶ A) (t : A ⟶ (P.mapHomologicalComplex _).obj A) (e : A ⟶ X)
    (s : X ⟶ Z) (m : Z ⟶ (P.mapHomologicalComplex _).obj Z)
    (h : ∀ n, e'.f n ≫ t.f n ≫ P.map (e.f n) ≫ P.map (s.f n) = s.f n ≫ m.f n) :
    (e' ≫ t ≫ (P.mapHomologicalComplex _).map e) ≫ (P.mapHomologicalComplex _).map s = s ≫ m := by
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
  exact h n

/-- The components of the first map of the open/closed sequence are counits. -/
lemma selfMapOpenClosedShortComplex_f_f (n : ℤ) :
    (selfMapOpenClosedShortComplex Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) i' j' hij' fW hfW
      (etaleModuleConstantComplex Λ kbar N)).f.f n =
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
        (etaleModuleConstantSheaf Λ (N.obj.X n) (Spec (.of kbar)))) := rfl

include sq in
/-- **The twist `τ₁` is compatible with the self-map twist** through the counit `S.f` of the
open/closed sequence: the hypothesis `hτ₁` of
`Stacks.EtaleCohomology.perfectDerivedTrace_selfMapOpenClosed_eq_zero`. -/
theorem extensionByZeroConstantOpenTwist_comp_f :
    extensionByZeroConstantOpenTwist Λ Y σ kbar p q hcard jV iW hij σV sq j' i' hij' gW hW gV hV N ≫
      ((etaleModuleDirectImage.{u, 0} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex
          _).map (selfMapOpenClosedShortComplex Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) i' j'
            hij' fW hfW (etaleModuleConstantComplex Λ kbar N)).f =
      (selfMapOpenClosedShortComplex Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) i' j' hij' fW
          hfW (etaleModuleConstantComplex Λ kbar N)).f ≫
        (NatTrans.mapHomologicalComplex (selfMapTwist.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius Y σ kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)) _).app
          (etaleModuleConstantComplex Λ kbar N).obj := by
  rw [extensionByZeroConstantOpenTwist]
  refine comp_mapHomologicalComplex_map_eq_of_f _ _ _ _ _ _ (fun n => ?_)
  have key := twistedFrobeniusTwist_extensionByZero_comp_counit Λ (N.obj.X n) Y σ kbar p q hcard
    jV iW hij σV sq j' i' hij' gW hW gV hV
  have key2 : (fieldBaseChangeExtensionByZeroConstantIso Λ (N.obj.X n) Y kbar jV iW hij j' i' hij'
      gW hW gV hV).inv ≫ twistedFrobeniusTwist.{u, 0} Λ Y σ kbar p q hcard _
        (extensionByZeroTwist Λ jV σV σ.left sq (etaleModuleConstantSheaf Λ (N.obj.X n) Y.left)
          (constantSelfMapTwist Λ (N.obj.X n) σ.left)) ≫
      (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
        (fieldBaseChangeExtensionByZeroConstantIso Λ (N.obj.X n) Y kbar jV iW hij j' i' hij' gW hW
          gV hV).hom ≫
      (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (etaleModuleConstantSheaf Λ (N.obj.X n) (Spec (.of kbar))))) =
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (etaleModuleConstantSheaf Λ (N.obj.X n) (Spec (.of kbar)))) ≫
        (selfMapTwist.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius Y σ kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)).app
            (etaleModuleConstantSheaf Λ (N.obj.X n) (Spec (.of kbar))) := by
    rw [← Functor.map_comp, key]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [NatTrans.mapHomologicalComplex_app_f, extensionByZeroConstantTwistedFrobeniusHC_f,
    fieldBaseChangeExtensionByZeroConstantComplexIso_inv_hom_f,
    fieldBaseChangeExtensionByZeroConstantComplexIso_hom_hom_f, selfMapOpenClosedShortComplex_f_f]
  exact key2

include hij hij' hW hV in
/-- Perfectness of `RΓ(Y_k̄, (j_{V!} j_V^{-1} N_Y)|_{Y_k̄})` is that of the cohomology with compact
support of `V_k̄` with coefficients in `N_{k̄}`. -/
lemma isPerfect_selfMapOpenCohomology_extensionByZeroConstant
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Y jV N))))))) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (selfMapOpenCohomology Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) j'
        (etaleModuleConstantComplex Λ kbar N)) := by
  refine StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} ?_ hZ
  exact DerivedCategory.Plus.ι.mapIso
    ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.mapIso
      ((etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso
          (fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij' gW hW gV
            hV N).symm)))

/-- **The twisted trace on `(j_{V!} j_V^{-1} N_Y)|_{Y_k̄}` is the trace of `τ₁`** on the cohomology
with compact support of `V_k̄`. -/
theorem perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_openTwist
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Y jV N)))))))
    (hp₁ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (selfMapOpenCohomology Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) j'
        (etaleModuleConstantComplex Λ kbar N))) :
    perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          (extensionByZeroConstantComplex Λ Y jV N))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            (extensionByZeroConstantComplex Λ Y jV N))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius Y σ kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Y jV N)))
          (extensionByZeroConstantTwistedFrobeniusHC Λ Y σ kbar p q hcard jV σV sq N)))) =
      perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm)
        _ (Functor.plusTwist (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius Y σ kbar p q hcard))
          (((etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, 0} Λ j').mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, 0} Λ
                (pullback.snd Y.hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
                (etaleModuleConstantComplex Λ kbar N)))).property)
          (extensionByZeroConstantOpenTwist Λ Y σ kbar p q hcard jV iW hij σV sq j' i' hij' gW hW
            gV hV N)))) := by
  set E := fieldBaseChangeExtensionByZeroConstantComplexIso Λ Y kbar jV iW hij j' i' hij' gW hW gV
    hV N with hE
  have hEE : E.hom.hom ≫ E.inv.hom = 𝟙 _ := congrArg (fun t => t.hom) E.hom_inv_id
  refine Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_iso
    (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm) E _ _ ?_ hZ hp₁
  ext n : 2
  show (extensionByZeroConstantTwistedFrobeniusHC Λ Y σ kbar p q hcard jV σV sq N).f n ≫ _ =
    E.hom.hom.f n ≫ (E.inv.hom.f n ≫
      (extensionByZeroConstantTwistedFrobeniusHC Λ Y σ kbar p q hcard jV σV sq N).f n ≫ _)
  rw [← Category.assoc (E.hom.hom.f n), ← HomologicalComplex.comp_f, hEE,
    HomologicalComplex.id_f, Category.id_comp]
  rfl

/-! ### The trace -/

variable [IsSepClosed kbar] (φW : W' ⟶ W') (wW : φW ≫ fW = fW)
  (hi : φW ≫ i' = i' ≫ twistedGeometricFrobenius Y σ kbar p q hcard) [Etale fW] [IsFinite fW]

include hij hij' hW hV hfW wW hi sq in
/-- **Step 9 of [Stacks, Tag 03UG] for the twisted Frobenius of `j_{V!} j_V^{-1} N_Y`.**  Let
`φ = σ̄ π̄` be the twisted Frobenius of `Y_k̄`, `V_k̄ ⊆ Y_k̄` the (`φ`-stable) open preimage of `V`
with closed complement `W_k̄` finite étale over `k̄` (`φ_W` the restriction of `φ`). If `φ` has no
fixed `k̄`-point on `V_k̄` and
`Tr(φ^* | RΓ(Y_k̄, f^{-1} N_{k̄})) = #Fix(φ) · Tr(id | Γ(k̄, N_{k̄}))` (Weil's formula, [Stacks,
Tag 03U1]), then the trace of `(σ̄ π̄)^*` on `RΓ(Y_k̄, (j_{V!} j_V^{-1} N_Y)|_{Y_k̄})` vanishes. -/
theorem perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_zero (φV : V' ⟶ V')
    (hj : φV ≫ j' = j' ≫ twistedGeometricFrobenius Y σ kbar p q hcard)
    (hVfix : ∀ y : Spec (.of kbar) ⟶ V',
      y ≫ j' ≫ pullback.snd Y.hom (specAlgebraMap k kbar) = 𝟙 _ → y ≫ φV ≠ y)
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Y jV N)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ
        (pullback.snd Y.hom (specAlgebraMap k kbar)) (etaleModuleConstantComplex Λ kbar N))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ fW
        (etaleModuleConstantComplex Λ kbar N))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex Λ (etaleModuleConstantComplex Λ kbar N).obj)))
    (hweil : perfectDerivedTrace Λ ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius Y σ kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)
          (etaleModuleConstantComplex Λ kbar N))) =
      Nat.card (fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius Y σ kbar p q hcard)) • perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _)) :
    perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          (extensionByZeroConstantComplex Λ Y jV N))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            (extensionByZeroConstantComplex Λ Y jV N))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius Y σ kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Y jV N)))
          (Functor.twistedBaseChangeTwistHC
            (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
            (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap σ kbar))
            (etaleModuleDirectImage.{u, 0} Λ σ.left)
            (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
            (automorphismBaseChange Λ Y σ kbar)
            (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap σ kbar)
              (geometricFrobeniusBaseChange Y kbar p q hcard)
              (twistedGeometricFrobenius Y σ kbar p q hcard) rfl)
            (extensionByZeroConstantComplex Λ Y jV N).obj
            (extensionByZeroConstantTwist Λ Y σ jV σV sq N)
            (extensionByZeroConstantTwist_comm Λ Y σ jV σV sq N))))) = 0 := by
  have hp₁ := isPerfect_selfMapOpenCohomology_extensionByZeroConstant Λ Y kbar jV iW hij j' i' hij'
    gW hW gV hV N hZ
  rw [perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_openTwist Λ Y σ kbar p q hcard
    jV iW hij σV sq j' i' hij' gW hW gV hV N hZ hp₁]
  exact perfectDerivedTrace_selfMapOpenClosed_eq_zero Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
    (twistedGeometricFrobenius Y σ kbar p q hcard)
    (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard) i' j' hij' fW hfW φW wW hi
    (etaleModuleConstantComplex Λ kbar N) φV hj hVfix _
    (extensionByZeroConstantOpenTwist_comp_f Λ Y σ kbar p q hcard jV iW hij σV sq j' i' hij' gW hW
      gV hV N fW hfW) hp₁ hp₂ hp₃ hΓ hweil

end OpenFix

end Stacks.EtaleCohomology

end
