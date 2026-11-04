module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalIdempotents
public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleRingKunneth
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictModulesMonoidalSheafTensor

/-!
# Local splittings on an open subspace

Let `U` be an open of a ringed space `X`, and let `P`, `P'` be complexes of modules on `U` whose
cohomology sheaves are those of complexes `K`, `K'` on `X` restricted to `U`. A local splitting of
`P`, `P'` over an open `V` of `U` is a local splitting of `K`, `K'` over the image of `V` in `X`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- An open set of `X` contained in the image of an open set of `U` is the image of an open set
of `U`. -/
public theorem forall_le_image {V : Opens (X.restrict U.isOpenEmbedding).carrier}
    {P : ∀ W : Opens X.carrier, W ≤ U.isOpenEmbedding.functor.obj V → Prop}
    (h : ∀ (W : Opens (X.restrict U.isOpenEmbedding).carrier) (hW : W ≤ V),
      P (U.isOpenEmbedding.functor.obj W) (U.isOpenEmbedding.functor.monotone hW))
    (W : Opens X.carrier) (hW : W ≤ U.isOpenEmbedding.functor.obj V) : P W hW := by
  have hWU : W ≤ U := hW.trans (isOpenMap_functor_obj_le U V)
  let W' : Opens (X.restrict U.isOpenEmbedding).carrier :=
    ⟨Subtype.val ⁻¹' (W : Set X.carrier), W.isOpen.preimage continuous_subtype_val⟩
  have hW'W : U.isOpenEmbedding.functor.obj W' = W := by
    ext z
    refine ⟨?_, fun hz => ⟨⟨z, hWU hz⟩, hz, rfl⟩⟩
    rintro ⟨v, hv, rfl⟩
    exact hv
  have hle : W' ≤ V := by
    intro v hv
    obtain ⟨v', hv', hvv'⟩ := hW hv
    exact (Subtype.ext hvv' : v' = v) ▸ hv'
  have := h W' hle
  clear_value W'
  subst hW'W
  exact this

variable {U}

/-- Multiplication by a section on a module isomorphic to another is transported along the
isomorphism. -/
private theorem smul_eq_inv_smul_hom {Y : RingedSpace.{u, u}} {F H : Mod Y.sheaf} (θ : F ≅ H)
    {W : Opens Y.carrier} (a : Y.presheaf.obj (op W)) (m : F.val.obj (op W)) :
    ringSec (U := op W) a • m =
      θ.inv.val.app (op W) (ringSec (U := op W) a • θ.hom.val.app (op W) m) := by
  have hm := congrArg (fun g : F ⟶ F => g.val.app (op W) m) θ.hom_inv_id
  have hl := (θ.inv.val.app (op W)).hom.map_smul (ringSec (U := op W) a) (θ.hom.val.app (op W) m)
  exact (congrArg (fun z : F.val.obj (op W) => ringSec (U := op W) a • z) hm).symm.trans hl.symm

/-- Multiplication by a section on the restriction of a module, read on the module. -/
public theorem smul_transport {G : Mod X.sheaf} {H : Mod (X.restrict U.isOpenEmbedding).sheaf}
    (θ : (restrictModules X U).obj G ≅ H) {V : Opens (X.restrict U.isOpenEmbedding).carrier}
    (s : (X.restrict U.isOpenEmbedding).presheaf.obj (op V)) (p : Prop) [Decidable p]
    (hs : ∀ {W : Opens (X.restrict U.isOpenEmbedding).carrier} (hW : W ≤ V)
      (m : H.val.obj (op W)), ringSec (U := op W) (resLE hW s) • m = if p then m else 0)
    {W : Opens X.carrier} (hW : W ≤ U.isOpenEmbedding.functor.obj V) (m : G.val.obj (op W)) :
    ringSec (U := op W) (resLE (X := X) hW s) • m = if p then m else 0 := by
  refine forall_le_image U (P := fun W hW => ∀ m : G.val.obj (op W),
    ringSec (U := op W) (resLE (X := X) hW s) • m = if p then m else 0) (fun W' hW' m => ?_) W hW m
  refine (smul_eq_inv_smul_hom θ (resLE hW' s) m).trans ?_
  rw [hs hW']
  split_ifs
  · exact congrArg (fun g : (restrictModules X U).obj G ⟶ (restrictModules X U).obj G =>
      g.val.app (op W') m) θ.hom_inv_id
  · exact map_zero _

/-- No section killing the restriction of a family of modules, read on the modules. -/
public theorem faithful_transport {G : ℤ → Mod X.sheaf}
    {H : ℤ → Mod (X.restrict U.isOpenEmbedding).sheaf}
    (θ : ∀ k, (restrictModules X U).obj (G k) ≅ H k)
    {V : Opens (X.restrict U.isOpenEmbedding).carrier}
    (hH : ∀ {W : Opens (X.restrict U.isOpenEmbedding).carrier} (_ : W ≤ V)
      (t : (X.restrict U.isOpenEmbedding).presheaf.obj (op W)),
      (∀ (k : ℤ) {W' : Opens (X.restrict U.isOpenEmbedding).carrier} (hW' : W' ≤ W)
        (m : (H k).val.obj (op W')), ringSec (U := op W') (resLE hW' t) • m = 0) → t = 0)
    {W : Opens X.carrier} (hW : W ≤ U.isOpenEmbedding.functor.obj V) (t : X.presheaf.obj (op W))
    (ht : ∀ (k : ℤ) {W' : Opens X.carrier} (hW' : W' ≤ W) (m : (G k).val.obj (op W')),
      ringSec (U := op W') (resLE hW' t) • m = 0) : t = 0 := by
  refine forall_le_image U (P := fun W _ => ∀ t : X.presheaf.obj (op W),
    (∀ (k : ℤ) {W' : Opens X.carrier} (hW' : W' ≤ W) (m : (G k).val.obj (op W')),
      ringSec (U := op W') (resLE hW' t) • m = 0) → t = 0) (fun W₀ hW₀ t ht => ?_) W hW t ht
  refine hH hW₀ t fun k W' hW' m => ?_
  refine (smul_eq_inv_smul_hom (θ k).symm (resLE hW' t) m).trans ?_
  exact (congrArg _ (ht k (U.isOpenEmbedding.functor.monotone hW') _)).trans (map_zero _)

variable (U) in
/-- A global section of `𝒪_X`, restricted to the open subspace `U`. -/
public abbrev resOpen (e : X.presheaf.obj (op ⊤)) :
    (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  globalRes e (U.isOpenEmbedding.functor.obj ⊤)

/-- Restriction to an open subspace carries multiplication by a global section to multiplication
by its restriction. -/
public theorem restrictModules_map_smulHom (e : X.presheaf.obj (op ⊤)) (G : Mod X.sheaf) :
    (restrictModules X U).map (smulHom e G) =
      smulHom (resOpen U e)
        ((restrictModules X U).obj G : Mod (X.restrict U.isOpenEmbedding).sheaf) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext
      fun (m : G.val.obj (op (U.isOpenEmbedding.functor.obj W.unop))) => ?_))
  exact congrArg (fun a : X.presheaf.obj (op (U.isOpenEmbedding.functor.obj W.unop)) =>
    ringSec (U := op (U.isOpenEmbedding.functor.obj W.unop)) a • m)
    (map_globalRes e (homOfLE (U.isOpenEmbedding.functor.monotone le_top)).op).symm

variable (U) in
/-- Restriction of the structure sheaf to an open subspace is the structure sheaf. -/
public def restrictUnitIso :
    ((restrictModules X U).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      X.sheaf)) : Mod (X.restrict U.isOpenEmbedding).sheaf) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (X.restrict U.isOpenEmbedding).sheaf) :=
  (@Functor.Monoidal.εIso _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) _ _
    (SheafOfModules.monoidalCategorySheafTensor (X.restrict U.isOpenEmbedding).sheaf)
    (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U)
    (Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidalSheafTensor X U)).symm

/-- **The pairing of a local splitting, read on `X`.** -/
public theorem pairing_transport {T : Mod X.sheaf} {T' : Mod (X.restrict U.isOpenEmbedding).sheaf}
    (θ : (restrictModules X U).obj T ≅ T') {V : Opens (X.restrict U.isOpenEmbedding).carrier}
    {e : X.presheaf.obj (op ⊤)} (he : IsIdempotentElem e)
    (A : Nonempty ((restrictModules (X.restrict U.isOpenEmbedding) V).obj T' ≅
      (restrictModules (X.restrict U.isOpenEmbedding) V).obj
        (splitObj (C := Mod (X.restrict U.isOpenEmbedding).sheaf)
          (smulHom (resOpen U e) (SheafOfModules.unit _))))) :
    Nonempty ((restrictModules X (U.isOpenEmbedding.functor.obj V)).obj T ≅
      (restrictModules X (U.isOpenEmbedding.functor.obj V)).obj
        (splitObj (C := Mod X.sheaf) (smulHom e (SheafOfModules.unit _)))) := by
  obtain ⟨α⟩ := A
  have hp : smulHom e (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ≫
      smulHom e (SheafOfModules.unit _) = smulHom e (SheafOfModules.unit _) := by
    rw [smulHom_comp, he.eq]
  let σ : (restrictModules X U).obj
      (splitObj (C := Mod X.sheaf) (smulHom e (SheafOfModules.unit _))) ≅
      splitObj (C := Mod (X.restrict U.isOpenEmbedding).sheaf)
        (smulHom (resOpen U e) (SheafOfModules.unit _)) :=
    mapSplitObjIso (restrictModules X U) hp ≪≫
      eqToIso (congrArg splitObj (restrictModules_map_smulHom e _)) ≪≫
      DerivedCategory.Invertible.splitObjIsoOfIso (restrictUnitIso U) (smulHom_naturality _ _)
  exact ⟨((RingedSpace.nestedModulesCompIso U V).app T).symm ≪≫
    (RingedSpace.nestedModulesEquivalence U V).functor.mapIso
      ((restrictModules (X.restrict U.isOpenEmbedding) V).mapIso θ ≪≫ α ≪≫
        (restrictModules (X.restrict U.isOpenEmbedding) V).mapIso σ.symm) ≪≫
    (RingedSpace.nestedModulesCompIso U V).app _⟩

variable (U) in
/-- **A local splitting on an open subspace is a local splitting on `X`.** -/
public def LocalSplitting.transport {K K' : CochainComplex (Mod X.sheaf) ℤ}
    {P P' : CochainComplex (Mod (X.restrict U.isOpenEmbedding).sheaf) ℤ}
    (θ : ∀ k, (restrictModules X U).obj (K.homology k) ≅ P.homology k)
    (θ' : ∀ k, (restrictModules X U).obj (K'.homology k) ≅ P'.homology k)
    {V : Opens (X.restrict U.isOpenEmbedding).carrier} (A : LocalSplitting P P' V) :
    LocalSplitting K K' (U.isOpenEmbedding.functor.obj V) where
  S := A.S
  f := A.f
  idem := A.idem
  ortho := A.ortho
  eq_zero := A.eq_zero
  sum_eq_one := A.sum_eq_one
  smul n k _ hW m := smul_transport (θ k) (A.f n) (k = n) (fun hW m => A.smul n k hW m) hW m
  smul' n k _ hW m := smul_transport (θ' k) (A.f n) (k = -n) (fun hW m => A.smul' n k hW m) hW m
  faithful hW t ht := faithful_transport θ (fun hW t ht => A.faithful hW t ht) hW t ht
  pairing n e he hres := by
    let := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    let := SheafOfModules.monoidalCategorySheafTensor (X.restrict U.isOpenEmbedding).sheaf
    let μ := @Functor.Monoidal.μIso _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) _ _
      (SheafOfModules.monoidalCategorySheafTensor (X.restrict U.isOpenEmbedding).sheaf)
      (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U)
      (Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidalSheafTensor X U)
      (K.homology n) (K'.homology (-n))
    exact pairing_transport (μ.symm ≪≫ @MonoidalCategory.tensorIso
      (Mod (X.restrict U.isOpenEmbedding).sheaf) _
      (SheafOfModules.monoidalCategorySheafTensor (X.restrict U.isOpenEmbedding).sheaf)
      _ _ _ _ (θ n) (θ' (-n))) he
      (A.pairing n (resOpen U e) (he.map (X.presheaf.map _).hom) fun hW =>
        (map_globalRes e _).trans (hres (U.isOpenEmbedding.functor.monotone hW)))

end Stacks.Cohomology.InvertibleDerived

end
