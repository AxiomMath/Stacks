module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualGlobal

/-!
# Algebraizing a map out of a completion on a Noetherian scheme

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. A morphism `α : G^∧ ⟶ (F_n)` whose
levelwise kernels and cokernels are annihilated by a power of `ℐ` is the completion of a morphism
`a : G ⟶ F` into a coherent `𝒪_X`-module, read through an isomorphism `β : F^∧ ≅ (F_n)`; the
triple `(F, a, β)` is unique up to a unique isomorphism among those for which the kernel and the
cokernel of `a` are annihilated by a power of `ℐ`. This is part (2) of Stacks 0889.

The module `F` and the isomorphism `β` are glued from the affine case by
`Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations`. The morphism `a` is
glued from the local morphisms `G|_U ⟶ F_U ≅ F|_U`, which agree on the overlaps because the local
algebraizations and the chart identifications are intertwined by the same comparison. The
uniqueness is glued as well: over each affine open the restrictions of two global triples are two
local algebraizations, related by a unique isomorphism, and the isomorphism over an affine open
restricts to the isomorphism over a smaller one, by uniqueness there.

## Main results

* `Stacks.Algebraization.completionMap_comp_eq_iff` — a morphism out of a completion is read
  through the canonical projections.
* `Stacks.Algebraization.restrictedAlgebraizationDual_iff` — the conditions on an isomorphism of
  two restricted algebraizations, read through the canonical projections.
* `Stacks.Algebraization.unique_algebraization_dual` — the uniqueness clause of Stacks 0889 (2) on
  a locally Noetherian scheme.
* `Stacks.Algebraization.exists_algebraization_dual` — the existence clause of Stacks 0889 (2) on
  a locally Noetherian scheme, with the kernel and the cokernel of `a` annihilated by a power of
  `ℐ` over each affine open.
* `Stacks.Algebraization.exists_unique_algebraization_dual_of_isNoetherian` — **Stacks 0889 (2)**.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Two cancellation patterns -/

section Helpers

variable {C : Type*} [Category C]

/-- Two morphisms followed by the two ends of an overlap comparison agree as soon as each of them
factors the corresponding end. -/
private theorem eq_of_overlapComparison {P M Ri Rj : C} {Li Lj : P ⟶ M} {Ai : M ⟶ Ri}
    {Aj : M ⟶ Rj} {dk : Ri ⟶ Rj} {Bi : P ⟶ Ri} {Bj : P ⟶ Rj} [Mono Aj]
    (hi : Li ≫ Ai = Bi) (hj : Lj ≫ Aj = Bj) (hA : Ai ≫ dk = Aj) (hB : Bi ≫ dk = Bj) :
    Li = Lj :=
  (cancel_mono Aj).1 (((congrArg (Li ≫ ·) hA.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dk) hi).trans hB))).trans hj.symm)

end Helpers

/-! ### Morphisms out of a completion through the projections -/

/-- **A morphism out of a completion, read through the canonical projections.** For a morphism
`D : F ⟶ F'` of coherent modules and morphisms `u : F^∧ ⟶ S`, `u' : F'^∧ ⟶ S` of inverse
systems, `D^∧ ≫ u' = u` exactly when `D ≫ π'_n ≫ u'_n = π_n ≫ u_n` at every level. -/
public theorem completionMap_comp_eq_iff {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (D : F ⟶ F')
    {S : ℕᵒᵖ ⥤ Y.Modules} (u : ((completionFunctor Y J).obj F).obj ⟶ S)
    (u' : ((completionFunctor Y J).obj F').obj ⟶ S) :
    ((completionFunctor Y J).map D).hom ≫ u' = u ↔
      ∀ n : ℕ, D.hom ≫ completionProjection Y J F' n ≫ u'.app (op n) =
        completionProjection Y J F n ≫ u.app (op n) := by
  have key : ∀ n : ℕ, completionProjection Y J F n ≫
      (((completionFunctor Y J).map D).hom ≫ u').app (op n) =
        D.hom ≫ completionProjection Y J F' n ≫ u'.app (op n) := fun n =>
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ u'.app (op n)) (completionFunctor_map_quotient Y J D n)).trans
        (Category.assoc _ _ _))
  refine ⟨fun h n => (key n).symm.trans (congrArg (fun t => completionProjection Y J F n ≫
    t.app (op n)) h), fun h => ?_⟩
  exact completionSystemHom_ext Y J F _ _ fun n => (key n).trans (h n)

/-- **The conditions on an isomorphism of two restricted algebraizations, read through the
projections.** Let `(F, a, β)` and `(F', a', β')` be two algebraizations of a map out of the
completion of `G`, and `D : F|_V ⟶ F'|_V` a morphism of their restrictions to an open subscheme.
Then `D` intertwines the restricted algebraizations exactly when it intertwines the restrictions of
`a` and `a'`, and of the composites `π_n ≫ β_n` and `π'_n ≫ β'_n`. -/
public theorem restrictedAlgebraizationDual_iff {X V : Scheme.{u}} (f : V ⟶ X) [IsOpenImmersion f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    {G F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) (a : G ⟶ F) (a' : G ⟶ F')
    (β : ((completionFunctor X I).obj F).obj ≅ Fsys.obj)
    (β' : ((completionFunctor X I).obj F').obj ≅ Fsys.obj)
    (D : restrictCoherentModules f F ⟶ restrictCoherentModules f F') :
    (restrictCoherentModulesMap f a ≫ D = restrictCoherentModulesMap f a' ∧
        ((completionFunctor V (I.comap f)).map D).hom ≫
            (restrictedAlgebraizationIsoDual f I Fsys F' β').hom =
          (restrictedAlgebraizationIsoDual f I Fsys F β).hom) ↔
      ((Scheme.Modules.restrictFunctor f).map a.hom ≫ D.hom =
          (Scheme.Modules.restrictFunctor f).map a'.hom ∧
        ∀ n : ℕ, D.hom ≫ (Scheme.Modules.restrictFunctor f).map
            (completionProjection X I F' n ≫ β'.hom.app (op n)) =
          (Scheme.Modules.restrictFunctor f).map
            (completionProjection X I F n ≫ β.hom.app (op n))) := by
  refine and_congr ⟨fun h => congrArg (fun t => t.hom) h,
    fun h => ObjectProperty.hom_ext _ h⟩ ((completionMap_comp_eq_iff _ D _ _).trans ?_)
  refine forall_congr' fun n => ?_
  rw [completionProjection_comp_restrictedAlgebraizationIsoDual,
    completionProjection_comp_restrictedAlgebraizationIsoDual]
  exact Iff.rfl

/-! ### Restricting equations down to a smaller open -/

/-- **An equation `D ≫ y|_U = x|_U` restricts down to `W ≤ U`**, with `D` carried to `W` through
the canonical comparison of the two routes down. -/
public theorem restrictDown_comp_restrictFunctor_map {X : Scheme.{u}} {U W : X.Opens}
    (hWU : W ≤ U) {M N P : X.Modules} (D : M.restrict U.ι ⟶ N.restrict U.ι) (x : M ⟶ P)
    (y : N ⟶ P)
    (h : D ≫ (Scheme.Modules.restrictFunctor U.ι).map y =
      (Scheme.Modules.restrictFunctor U.ι).map x) :
    ((restrictDownIso hWU M).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map D ≫
        (restrictDownIso hWU N).inv) ≫ (Scheme.Modules.restrictFunctor W.ι).map y =
      (Scheme.Modules.restrictFunctor W.ι).map x := by
  rw [← cancel_mono (restrictDownIso hWU P).hom, Category.assoc,
    restrictDownIso_hom_naturality hWU y, restrictDownIso_hom_naturality hWU x]
  simp [← Functor.map_comp, h]

/-- **An equation `x|_U ≫ D = y|_U` restricts down to `W ≤ U`.** -/
public theorem restrictFunctor_map_comp_restrictDown {X : Scheme.{u}} {U W : X.Opens}
    (hWU : W ≤ U) {P M N : X.Modules} (D : M.restrict U.ι ⟶ N.restrict U.ι) (x : P ⟶ M)
    (y : P ⟶ N)
    (h : (Scheme.Modules.restrictFunctor U.ι).map x ≫ D =
      (Scheme.Modules.restrictFunctor U.ι).map y) :
    (Scheme.Modules.restrictFunctor W.ι).map x ≫ (restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map D ≫ (restrictDownIso hWU N).inv =
      (Scheme.Modules.restrictFunctor W.ι).map y := by
  rw [← cancel_mono (restrictDownIso hWU N).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, restrictDownIso_hom_naturality hWU x, Category.assoc,
    ← Functor.map_comp, h, restrictDownIso_hom_naturality hWU y]

/-- **A local composite carried down to `W ≤ U`.** If `ψ ≫ c = b` over `U`, then `ψ` carried down
to `W`, followed by `c` carried down, is `b` carried down. -/
public theorem restrictDown_comp_restrictDown {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {P M : X.Modules} {Q : U.toScheme.Modules} (ψ : P.restrict U.ι ⟶ M.restrict U.ι)
    (c : M.restrict U.ι ⟶ Q) (b : P.restrict U.ι ⟶ Q) (h : ψ ≫ c = b) :
    ((restrictDownIso hWU P).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map ψ ≫
        (restrictDownIso hWU M).inv) ≫ (restrictDownIso hWU M).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map c =
      (restrictDownIso hWU P).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b := by
  simp [← Functor.map_comp, h]

/-! ### Covers by the affine opens -/

/-- The affine opens of a scheme cover it, as images of their inclusions. -/
public theorem iSup_affineOpens_ι_image_top (X : Scheme.{u}) :
    ⨆ i : X.affineOpens, i.1.ι ''ᵁ (⊤ : i.1.toScheme.Opens) = ⊤ := by
  simpa only [Scheme.Opens.ι_image_top] using iSup_affineOpens_eq_top X

/-- **A morphism of sheaves of modules is determined by its restrictions to the affine opens.** -/
public theorem hom_ext_of_affineOpens {X : Scheme.{u}} {M N : X.Modules} (u v : M ⟶ N)
    (h : ∀ i : X.affineOpens, (Scheme.Modules.restrictFunctor i.1.ι).map u =
      (Scheme.Modules.restrictFunctor i.1.ι).map v) : u = v :=
  Stacks.Coherent.hom_ext_of_restrictCover (fun i : X.affineOpens => i.1.ι)
    (iSup_affineOpens_ι_image_top X) u v h

/-- **A family of morphisms of the restrictions to the affine opens, compatible with carrying down
to a smaller affine open, is the family of restrictions of one morphism.** -/
public theorem exists_hom_of_restrictDown {X : Scheme.{u}} {M N : X.Modules}
    (ψ : ∀ i : X.affineOpens, M.restrict i.1.ι ⟶ N.restrict i.1.ι)
    (hψ : ∀ (i j k : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      (restrictDownIso hki M).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE hki)).map (ψ i) ≫
          (restrictDownIso hki N).inv =
        (restrictDownIso hkj M).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE hkj)).map (ψ j) ≫
          (restrictDownIso hkj N).inv) :
    ∃ φ : M ⟶ N, ∀ i : X.affineOpens, (Scheme.Modules.restrictFunctor i.1.ι).map φ = ψ i := by
  obtain ⟨φ, hφ, -⟩ := Stacks.Coherent.existsUnique_hom_of_affineComparison
    (iSup_affineOpens_eq_top X) ψ fun i j k hki hkj =>
      localAppOpen_eq_of_restrictDown_eq hki hkj (ψ i) (ψ j) (hψ i j k hki hkj)
  exact ⟨φ, fun i => restrictHom_ext_of_localAppOpen i.1 _ _ fun V hV =>
    (Stacks.Coherent.localAppOpen_restrictFunctor_map i.1 φ hV).trans (hφ i V hV)⟩

/-! ### The uniqueness clause -/

/-- **The uniqueness clause of Stacks 0889 (2).** Let `X` be a locally Noetherian scheme and
`α : G^∧ ⟶ (F_n)` a morphism of coherent `ℐ`-adic systems. Two triples `(F, a, β)` and
`(F', a', β')`, with `a : G ⟶ F` a morphism of coherent modules whose kernel and cokernel are
annihilated by a power of `ℐ`, `β : F^∧ ≅ (F_n)` and `α = β ∘ a^∧`, and likewise for the second,
are related by a unique isomorphism `F ≅ F'` compatible with `a, a'` and with `β, β'`.

Over each affine open the restrictions of the two triples are local algebraizations, related by a
unique isomorphism by the affine case. The isomorphism over an affine open, carried down to a
smaller affine open, is again such an isomorphism there, so it is the one over the smaller open;
hence the local isomorphisms glue. The compatibilities of the glued morphism, and its uniqueness,
are checked on the affine opens. -/
public theorem unique_algebraization_dual {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (a : G ⟶ F) (a' : G ⟶ F')
    (β : ((completionFunctor X I).obj F).obj ≅ Fsys.obj)
    (β' : ((completionFunctor X I).obj F').obj ≅ Fsys.obj)
    (hα : α = ((completionFunctor X I).map a).hom ≫ β.hom)
    (hα' : α = ((completionFunctor X I).map a').hom ≫ β'.hom)
    (hKa : IsPowerAnnihilated I (kernel (C := X.Modules) a.hom))
    (hCa : IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom))
    (hKa' : IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom))
    (hCa' : IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom)) :
    ∃! d : F ≅ F',
      a ≫ d.hom = a' ∧ ((completionFunctor X I).map d.hom).hom ≫ β'.hom = β.hom := by
  set x : ∀ n : ℕ, F.obj ⟶ Fsys.obj.obj (op n) :=
    fun n => completionProjection X I F n ≫ β.hom.app (op n)
  set y : ∀ n : ℕ, F'.obj ⟶ Fsys.obj.obj (op n) :=
    fun n => completionProjection X I F' n ≫ β'.hom.app (op n)
  have hloc : ∀ i : X.affineOpens, ∃! d : restrictCoherentModules i.1.ι F ≅
      restrictCoherentModules i.1.ι F',
      restrictCoherentModulesMap i.1.ι a ≫ d.hom = restrictCoherentModulesMap i.1.ι a' ∧
        ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map d.hom).hom ≫
            (restrictedAlgebraizationIsoDual i.1.ι I Fsys F' β').hom =
          (restrictedAlgebraizationIsoDual i.1.ι I Fsys F β).hom := fun i =>
    unique_local_algebraization_dual I G Fsys α i _ _ _ _ _ _
      (restrictedSystemMapDual_eq_of_algebraization i.1.ι I G Fsys α F a β hα)
      (restrictedSystemMapDual_eq_of_algebraization i.1.ι I G Fsys α F' a' β' hα')
      (isPowerAnnihilated_kernel_restrictCoherentModulesMap i.1.ι I a hKa)
      (isPowerAnnihilated_cokernel_restrictCoherentModulesMap i.1.ι I a hCa)
      (isPowerAnnihilated_kernel_restrictCoherentModulesMap i.1.ι I a' hKa')
      (isPowerAnnihilated_cokernel_restrictCoherentModulesMap i.1.ι I a' hCa')
  choose dl hdl huniq using hloc
  have hLS : ∀ i : X.affineOpens,
      (Scheme.Modules.restrictFunctor i.1.ι).map a.hom ≫ (dl i).hom.hom =
          (Scheme.Modules.restrictFunctor i.1.ι).map a'.hom ∧
        ∀ n : ℕ, (dl i).hom.hom ≫ (Scheme.Modules.restrictFunctor i.1.ι).map (y n) =
          (Scheme.Modules.restrictFunctor i.1.ι).map (x n) := fun i =>
    (restrictedAlgebraizationDual_iff i.1.ι I Fsys a a' β β' (dl i).hom).1 (hdl i)
  have key : ∀ (i k : X.affineOpens) (hki : k.1 ≤ i.1),
      (restrictDownIso hki F.obj).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hki)).map (dl i).hom.hom ≫
            (restrictDownIso hki F'.obj).inv = (dl k).hom.hom := by
    intro i k hki
    let T : restrictCoherentModules k.1.ι F ≅ restrictCoherentModules k.1.ι F' :=
      ObjectProperty.isoMk _ (restrictDownIso hki F.obj ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hki)).mapIso (Stacks.underlyingObjIso (dl i)) ≪≫
          (restrictDownIso hki F'.obj).symm)
    have hT := (restrictedAlgebraizationDual_iff k.1.ι I Fsys a a' β β' T.hom).2
      ⟨restrictFunctor_map_comp_restrictDown hki (dl i).hom.hom a.hom a'.hom (hLS i).1,
        fun n => restrictDown_comp_restrictFunctor_map hki (dl i).hom.hom (x n) (y n)
          ((hLS i).2 n)⟩
    exact congrArg (fun e => e.hom.hom) (huniq k T hT)
  obtain ⟨φ, hφ⟩ := exists_hom_of_restrictDown (fun i => (dl i).hom.hom)
    fun i j k hki hkj => (key i k hki).trans (key j k hkj).symm
  have hiso : IsIso φ := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict φ
      (fun i : X.affineOpens => i.1) (IsOpenCover.mk (iSup_affineOpens_eq_top X)) fun i => ?_
    rw [hφ i]
    exact (inferInstance : IsIso (Stacks.underlyingObjIso (dl i)).hom)
  refine ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _ φ hiso), ⟨ObjectProperty.hom_ext _ ?_, ?_⟩, ?_⟩
  · refine hom_ext_of_affineOpens (a.hom ≫ φ) a'.hom fun i => ?_
    exact ((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _).trans
      ((congrArg (_ ≫ ·) (hφ i)).trans (hLS i).1)
  · refine (completionMap_comp_eq_iff I _ β.hom β'.hom).2 fun n => ?_
    refine hom_ext_of_affineOpens (φ ≫ y n) (x n) fun i => ?_
    exact ((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _).trans
      ((congrArg (· ≫ _) (hφ i)).trans ((hLS i).2 n))
  · rintro d ⟨hda, hdβ⟩
    refine Iso.ext (ObjectProperty.hom_ext _ (hom_ext_of_affineOpens _ φ fun i => ?_))
    rw [hφ i]
    let Ti : restrictCoherentModules i.1.ι F ≅ restrictCoherentModules i.1.ι F' :=
      ObjectProperty.isoMk _
        ((Scheme.Modules.restrictFunctor i.1.ι).mapIso (Stacks.underlyingObjIso d))
    have hTi := (restrictedAlgebraizationDual_iff i.1.ι I Fsys a a' β β' Ti.hom).2
      ⟨((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _).symm.trans
          (congrArg (fun t => (Scheme.Modules.restrictFunctor i.1.ι).map
            (InducedCategory.Hom.hom t)) hda),
        fun n => ((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.restrictFunctor i.1.ι).map
            ((completionMap_comp_eq_iff I d.hom β.hom β'.hom).1 hdβ n))⟩
    exact congrArg (fun e => e.hom.hom) (huniq i Ti hTi)

/-! ### The existence clause -/

/-- **The existence clause of Stacks 0889 (2) on a locally Noetherian scheme.** A morphism
`α : G^∧ ⟶ (F_n)` whose levelwise kernels and cokernels are annihilated by a power of `ℐ` is
`β ∘ a^∧` for a morphism `a : G ⟶ F` of coherent `𝒪_X`-modules and an isomorphism
`β : F^∧ ≅ (F_n)`, and over each affine open `U` the kernel and the cokernel of `a` are annihilated
by a power of `ℐ|_U`.

`F` and `β` are glued from the local algebraizations `b U : G|_U ⟶ F_U` by
`Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations`, which also provides
chart identifications `F|_U ≅ F_U`. The morphism `a` is glued from the composites of the `b U`
with the inverse chart identifications: over an affine open inside two charts, both composites are
determined by the comparison of the two local algebraizations, which intertwines the transported
`b`'s and the transported charts alike. The factorization of `α` is checked on the affine opens
after the canonical projections, and over `U` the kernel and the cokernel of `a` are those of
`b U`. -/
public theorem exists_algebraization_dual {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
      (β : ((completionFunctor X I).obj F).obj ≅ Fsys.obj),
      α = ((completionFunctor X I).map a).hom ≫ β.hom ∧
        ∀ i : X.affineOpens,
          IsPowerAnnihilated (I.comap i.1.ι)
              ((Scheme.Modules.restrictFunctor i.1.ι).obj (kernel (C := X.Modules) a.hom)) ∧
            IsPowerAnnihilated (I.comap i.1.ι)
              ((Scheme.Modules.restrictFunctor i.1.ι).obj (cokernel (C := X.Modules) a.hom)) := by
  choose Fl b β h using fun i : X.affineOpens => exists_local_algebraization_dual I G Fsys α hα i
  obtain ⟨M, chart, e, hd, he⟩ := exists_glued_completionIso_of_localAlgebraizations I G Fsys α
    Fl b β (fun i => (h i).1) (fun i => (h i).2.1) fun i => (h i).2.2
  have hci : ∀ i : X.affineOpens, (chart i).inv.hom ≫ (chart i).hom.hom = 𝟙 _ :=
    fun i => ObjectProperty.isoInv_hom_id_hom (chart i)
  set ψ : ∀ i : X.affineOpens,
      Scheme.Modules.restrict G.obj i.1.ι ⟶ Scheme.Modules.restrict M.obj i.1.ι :=
    fun i => (b i).hom ≫ (chart i).inv.hom
  have hψc : ∀ i : X.affineOpens, ψ i ≫ (chart i).hom.hom = (b i).hom := fun i =>
    (Category.assoc _ _ _).trans ((congrArg ((b i).hom ≫ ·) (hci i)).trans (Category.comp_id _))
  obtain ⟨φ, hφ⟩ := exists_hom_of_restrictDown ψ fun i j k hki hkj => by
    obtain ⟨dk, hdb, hdc⟩ := hd k i j hki hkj
    have hmono : Mono ((restrictDownIso hkj M.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hkj)).map (chart j).hom.hom) :=
      (inferInstance : Mono (restrictDownIso hkj M.obj ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hkj)).mapIso
          (Stacks.underlyingObjIso (chart j))).hom)
    exact eq_of_overlapComparison
      ((restrictDown_comp_restrictDown hki (ψ i) (chart i).hom.hom (b i).hom (hψc i)).trans
        (restrictedAlgebraizationMapOfLE_hom_eq_restrictDown hki (b i)))
      ((restrictDown_comp_restrictDown hkj (ψ j) (chart j).hom.hom (b j).hom (hψc j)).trans
        (restrictedAlgebraizationMapOfLE_hom_eq_restrictDown hkj (b j)))
      (((congrArg (· ≫ dk.hom.hom)
          (restrictedAlgebraizationMapOfLE_hom_eq_restrictDown hki (chart i).hom))).trans
        ((congrArg InducedCategory.Hom.hom hdc).trans
          (restrictedAlgebraizationMapOfLE_hom_eq_restrictDown hkj (chart j).hom).symm))
      (congrArg InducedCategory.Hom.hom hdb)
  have hφc : ∀ i : X.affineOpens,
      (Scheme.Modules.restrictFunctor i.1.ι).map φ ≫ (chart i).hom.hom = (b i).hom :=
    fun i => (congrArg (· ≫ (chart i).hom.hom) (hφ i)).trans (hψc i)
  let a : G ⟶ M := ObjectProperty.homMk φ
  refine ⟨M, a, Stacks.underlyingObjIso e,
    ((completionMap_comp_eq_iff I a α (Stacks.underlyingObjIso e).hom).2 fun n => ?_).symm,
    fun i => ?_⟩
  · refine hom_ext_of_affineOpens _ _ fun i => ?_
    have hei : (Scheme.Modules.restrictFunctor i.1.ι).map (e.hom.hom.app (op n)) =
        (completionRestrictChartIso I i.1 M Fsys (Fl i) (chart i) (β i)).hom.hom.app (op n) :=
      congrArg (fun t => t.hom.app (op n)) (he i)
    have hP := completionProjection_comp_completionRestrictChartIso I i.1 M Fsys (Fl i) (chart i)
      (β i) n
    have hb := (completionMap_comp_eq_iff _ (b i) _ _).1 (h i).1.symm n
    refine ((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((Scheme.Modules.restrictFunctor i.1.ι).map_comp _ _)).trans ?_
    refine (congrArg (fun t => _ ≫ _ ≫ t) hei).trans ?_
    refine (congrArg (_ ≫ ·) hP).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (hφc i)).trans ?_
    exact hb.trans (completionProjection_comp_restrictedSystemMapDual i.1.ι I G Fsys α n)
  · have hfl : PreservesFiniteLimits (Scheme.Modules.restrictFunctor i.1.ι) :=
      AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor i.1.ι
    have hpl : PreservesLimitsOfShape WalkingParallelPair
        (Scheme.Modules.restrictFunctor i.1.ι) := hfl.preservesFiniteLimits _
    have hc : IsIso (chart i).hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
    obtain ⟨nK, hnK⟩ := (h i).2.1
    obtain ⟨nC, hnC⟩ := (h i).2.2
    refine ⟨⟨nK, idealPowerMultiple_eq_bot_of_iso (I.comap i.1.ι) ?_ nK hnK⟩,
      ⟨nC, idealPowerMultiple_eq_bot_of_iso (I.comap i.1.ι) ?_ nC hnC⟩⟩
    · exact PreservesKernel.iso (Scheme.Modules.restrictFunctor i.1.ι) φ ≪≫
        (kernelCompMono _ (chart i).hom.hom).symm ≪≫ kernelIsoOfEq (hφc i)
    · exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor i.1.ι) φ ≪≫
        (cokernelCompIsIso _ (chart i).hom.hom).symm ≪≫ cokernelIsoOfEq (hφc i)

/-! ### Stacks 0889 (2) -/

/-- **Stacks 0889 (2).** Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `G` a
coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. A morphism `α : G^∧ ⟶ (F_n)` whose
levelwise kernels and cokernels are annihilated by a power of `ℐ` admits a triple `(F, a, β)`,
unique up to a unique isomorphism, with `F` a coherent `𝒪_X`-module, `a : G ⟶ F` a morphism whose
kernel and cokernel are annihilated by a power of `ℐ`, `β : F^∧ ≅ (F_n)` an isomorphism, and
`α = β ∘ a^∧`.

The existence is `Stacks.Algebraization.exists_algebraization_dual`, whose affine-local
annihilation of the kernel and the cokernel of `a` becomes annihilation by a single power of `ℐ`
by `Stacks.Algebraization.isPowerAnnihilated_of_restrict`, using that `X` is quasi-compact. The
uniqueness is `Stacks.Algebraization.unique_algebraization_dual`. -/
@[stacks 0889 "part (2): algebraization of a map out of a completion"]
public theorem exists_unique_algebraization_dual_of_isNoetherian {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
      (β : ((completionFunctor X I).obj F).obj ≅ Fsys.obj),
      (α = ((completionFunctor X I).map a).hom ≫ β.hom ∧
          IsPowerAnnihilated I (kernel (C := X.Modules) a.hom) ∧
            IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom)) ∧
        ∀ (F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a' : G ⟶ F')
            (β' : ((completionFunctor X I).obj F').obj ≅ Fsys.obj),
          α = ((completionFunctor X I).map a').hom ≫ β'.hom →
            IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom) →
              IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom) →
                ∃! d : F ≅ F',
                  a ≫ d.hom = a' ∧
                    ((completionFunctor X I).map d.hom).hom ≫ β'.hom = β.hom := by
  obtain ⟨F, a, β, hfac, hann⟩ := exists_algebraization_dual I G Fsys α hα
  have hK := isPowerAnnihilated_of_restrict I _ fun i => (hann i).1
  have hC := isPowerAnnihilated_of_restrict I _ fun i => (hann i).2
  exact ⟨F, a, β, ⟨hfac, hK, hC⟩, fun F' a' β' hfac' hK' hC' =>
    unique_algebraization_dual I G Fsys α F F' a a' β β' hfac hfac' hK hC hK' hC'⟩

end Stacks.Algebraization

end
