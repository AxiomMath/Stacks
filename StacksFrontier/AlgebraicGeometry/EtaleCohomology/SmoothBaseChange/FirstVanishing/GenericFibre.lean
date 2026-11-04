module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GaloisCoverKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre

/-!
# Killing a class of `H¹` of the geometric generic fibre by a finite étale cover

This is the final case `q = 1` of the second proof of the smooth base change theorem (Stacks
0EYU), after the reductions: `S` is an integral normal scheme whose generic point has an
algebraically closed residue field `L`, `f : U ⟶ S` is smooth with geometrically connected fibres
and a section, its generic fibre is a curve, `K ⊇ L` is algebraically closed, and
`ξ ∈ H¹(U ×_S Spec K, ℤ/dℤ)` with `d` invertible on `S`. Then `ξ` dies on `Y' ×_U (U ×_S Spec K)`
for a finite étale surjective `Y' ⟶ U`.

The proof: `H¹(U_L, ℤ/dℤ) = H¹(U_K, ℤ/dℤ)` (Stacks 03SC (6), an identification Stacks
attributes to Lemma 0A5E), so `ξ` comes from `U_L`, where a finite étale Galois cover of order
dividing `d` kills it
(`Stacks.EtaleCohomology.exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero`); by Stacks 0EZJ
that cover extends to a finite étale Galois cover `Y'` of `U`, and `ξ` dies on `Y'_K`.

Both cited results enter as hypotheses, `CurveCohomologyAlgClosedInvariance` (Stacks 03SC (6))
and `GaloisCoversExtendFromGenericFiber` (Stacks 0EZJ).

## Main results

All in the namespace `Stacks.EtaleCohomology.SmoothBaseChange`.

* `exists_spec_map_comp_fromSpecResidueField_eq`: a dominant morphism from the spectrum of a field
  to an integral scheme factors through the generic point.
* `isNormal_and_irreducibleSpace_fiber`: the fibres of a smooth morphism with geometrically
  connected fibres are normal and irreducible.
* `exists_finiteEtale_mapExactFunctor_eq_zero_of_genericFibre`: the statement above.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- A class whose image under an exact functor vanishes after composing with two isomorphisms in
degree zero already has vanishing image. -/
theorem mapExactFunctor_eq_zero_of_mk₀_comp_comp_mk₀ {C D : Type*} [Category* C] [Abelian C]
    [Category* D] [Abelian D] [HasExt.{u + 1} C] [HasExt.{u + 1} D] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] {X X' Y Y' : C} (α : X' ⟶ X)
    [IsIso α] (β : Y ⟶ Y') [IsIso β] {n : ℕ} (x : Ext.{u + 1} X Y n)
    (h : ((Ext.mk₀ α).comp (x.comp (Ext.mk₀ β) (add_zero n)) (zero_add n)).mapExactFunctor L =
      0) :
    x.mapExactFunctor L = 0 := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mk₀] at h
  have h' := congrArg (fun y => (Ext.mk₀ (inv (L.map α))).comp
    (y.comp (Ext.mk₀ (inv (L.map β))) (add_zero n)) (zero_add n)) h
  simp only [Ext.zero_comp, Ext.comp_zero] at h'
  rwa [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    IsIso.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id,
    Ext.mk₀_id_comp] at h'

/-- A unit of a field which is the image of a natural number `d` makes `d` prime to the
characteristic. -/
theorem ringChar_eq_zero_or_coprime_of_isUnit {k : Type*} [Field k] {d : ℕ}
    (hd : IsUnit (d : k)) : ringChar k = 0 ∨ d.Coprime (ringChar k) := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · exact .inr (hp.coprime_iff_not_dvd.2 fun hdvd =>
      hd.ne_zero ((CharP.cast_eq_zero_iff k (ringChar k) d).2 hdvd)).symm
  · exact .inl h0

/-- The fibre of a smooth morphism over a point is smooth over the residue field. -/
private local instance smooth_fiberToSpecResidueField
    {S U : Scheme.{u}} (f : U ⟶ S) (s : S) [Smooth f] :
    Smooth (f.fiberToSpecResidueField s) :=
  inferInstanceAs (Smooth (pullback.snd f (S.fromSpecResidueField s)))

/-- The fibre of a separated morphism over a point is separated over the residue field. -/
private local instance isSeparated_fiberToSpecResidueField
    {S U : Scheme.{u}} (f : U ⟶ S) (s : S) [IsSeparated f] :
    IsSeparated (f.fiberToSpecResidueField s) :=
  inferInstanceAs (IsSeparated (pullback.snd f (S.fromSpecResidueField s)))

/-- The fibre of a morphism locally of finite type over a point is locally of finite type over
the residue field. -/
private local instance locallyOfFiniteType_fiberToSpecResidueField
    {S U : Scheme.{u}} (f : U ⟶ S) (s : S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))

/-- The fibre of a quasi-compact morphism over a point is quasi-compact over the residue field. -/
private local instance quasiCompact_fiberToSpecResidueField
    {S U : Scheme.{u}} (f : U ⟶ S) (s : S) [QuasiCompact f] :
    QuasiCompact (f.fiberToSpecResidueField s) :=
  inferInstanceAs (QuasiCompact (pullback.snd f (S.fromSpecResidueField s)))

/-- A morphism from the spectrum of a field to an integral scheme which is dominant hits the
generic point, so it factors through the spectrum of the function field. -/
theorem exists_spec_map_comp_fromSpecResidueField_eq {S : Scheme.{u}} [IsIntegral S]
    {K : Type u} [Field K] (g : Spec (.of K) ⟶ S) [IsDominant g] :
    ∃ φ : S.residueField (genericPoint S) ⟶ .of K,
      Spec.map φ ≫ S.fromSpecResidueField (genericPoint S) = g := by
  have hgen : g (IsLocalRing.closedPoint K) = genericPoint S := by
    refine ((genericPoint_spec S).eq ?_).symm
    rw [isGenericPoint_iff_specializes]
    intro y
    have hy : y ∈ closure (Set.range g) := g.denseRange.closure_eq ▸ Set.mem_univ y
    have hr : Set.range g = {g (IsLocalRing.closedPoint K)} :=
      Set.range_eq_singleton fun a => by rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
    rw [hr, ← specializes_iff_mem_closure] at hy
    exact iff_of_true hy trivial
  rw [← hgen]
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S g⟩

/-- **The fibres of a smooth, quasi-compact morphism with geometrically connected fibres are
irreducible and normal**: a fibre is smooth over a field, hence normal and Noetherian, and it is
connected. -/
theorem isNormal_and_irreducibleSpace_fiber {S U : Scheme.{u}} (f : U ⟶ S) [QuasiCompact f]
    [Smooth f] [GeometricallyConnected f] (s : S) :
    IsNormal (f.fiber s) ∧ IrreducibleSpace (f.fiber s) := by
  have : IsNormal (Spec (S.residueField s)) :=
    isNormal_spec_of_isIntegrallyClosed (S.residueField s)
  have : IsNormal (f.fiber s) := isNormal_of_smooth (f.fiberToSpecResidueField s)
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have : IsNoetherian (f.fiber s) := {}
  exact ⟨inferInstance, irreducibleSpace_of_isNormal_of_connectedSpace _ inferInstance⟩

/-- **A class of `H¹` of the generic fibre is killed by a finite étale cover of the total
space**: a Galois cover of the generic fibre of order dividing `d` kills it, and by Stacks 0EZJ
that cover extends to a finite étale Galois cover of `U`. -/
private theorem exists_finiteEtale_mapExactFunctor_eq_zero_of_fiber
    (h0EZJ : GaloisCoversExtendFromGenericFiber.{u}) {S U : Scheme.{u}} (f : U ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ U) (hσ : σ ≫ f = 𝟙 S) [IsAlgClosed (S.residueField (genericPoint S))]
    (d : ℕ) (hd : 0 < d) (hdS : ∀ s : S, IsUnit (d : S.residueField s))
    (ξ : Sheaf.H.{u + 1} (FirstFailureDiagram.constantZMod (f.fiber (genericPoint S)) d) 1) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ U), IsFinite π ∧ Etale π ∧ Surjective π ∧
      ∀ ⦃W' : Scheme.{u}⦄ (n : W' ⟶ f.fiber (genericPoint S)) (t : W' ⟶ Y'),
        n ≫ f.fiberι (genericPoint S) = t ≫ π →
        ξ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} n) = 0 := by
  obtain ⟨hnorm, hirr⟩ := isNormal_and_irreducibleSpace_fiber f (genericPoint S)
  let x : GeometricPoint (f.fiber (genericPoint S)) :=
    { residueField := S.residueField (genericPoint S)
      hom := genericFiberSection f σ hσ }
  obtain ⟨G, _, _, hGd, Z, z, hz, hZ⟩ := exists_finiteEtaleGaloisCover_mapExactFunctor_eq_zero
    (@isGeometricallyUnibranch_of_isNormal _ hnorm) d hd ξ x
  obtain ⟨Y', eY, -⟩ := h0EZJ f σ hσ G
    (fun s => isUnit_of_dvd_unit (Nat.cast_dvd_cast hGd) (hdS s)) Z z hz
  have : ConnectedSpace U := GeometricallyConnected.connectedSpace (f := f) f.isOpenMap
  refine ⟨Y'.obj.left, Y'.obj.hom, Y'.obj.prop.1, Y'.obj.prop.2,
    ⟨surjective_hom_of_finiteEtaleOver Y'.obj⟩, fun W' n t hnt => ?_⟩
  let w := pullback.lift t n hnt.symm ≫ eY.hom.left
  have hw : w ≫ Z.obj.hom = n := (Category.assoc _ _ _).trans <|
    (pullback.lift t n hnt.symm ≫= MorphismProperty.Over.w eY.hom).trans (pullback.lift_snd _ _ _)
  rw [← hw, ← mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff]
  exact (congrArg (fun y => Ext.mapExactFunctor (etaleAbelianInverseImage.{u, 0} w) y) hZ).trans
    (Ext.mapExactFunctor_zero _ _ _ _)

/-- **A class of `H¹` of a geometric fibre over the generic point is killed by a finite étale
cover of the total space.** Let `S` be a quasi-compact, quasi-separated, integral normal scheme
whose generic point has an algebraically closed residue field `L`, and let `f : U ⟶ S` be a
separated, quasi-compact, smooth morphism with geometrically connected fibres and a section,
whose generic fibre has dimension at most one. Let `K ⊇ L` be an algebraically closed field,
`W = U ×_S Spec K` and `d` invertible on `S`. Every class `κ ∈ H¹(W, ℤ/dℤ)` dies on
`W ×_U Y'` for some finite étale surjective `Y' ⟶ U`.

By Stacks 03SC (6) the class comes from `H¹(U_L, ℤ/dℤ)`, where it is killed by a finite étale
Galois cover of `U_L` of order dividing `d`; by Stacks 0EZJ that cover extends to a finite étale
Galois cover `Y'` of `U`. -/
theorem exists_finiteEtale_mapExactFunctor_eq_zero_of_genericFibre
    (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EZJ : GaloisCoversExtendFromGenericFiber.{u}) {S U : Scheme.{u}} (f : U ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] [GeometricallyConnected f] [IsSeparated f]
    (σ : S ⟶ U) (hσ : σ ≫ f = 𝟙 S) [IsAlgClosed (S.residueField (genericPoint S))]
    (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
    (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S) [IsDominant g]
    {W : Scheme.{u}} (ι : W ⟶ U) (e : W ⟶ Spec (.of K)) (sq : IsPullback ι e f g)
    (d : ℕ) (hd : 0 < d) (hdS : ∀ s : S, IsUnit (d : S.residueField s))
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (eA : A ≅ FirstFailureDiagram.constantZMod W d) (κ : Sheaf.H.{u + 1} A 1) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ U), IsFinite π ∧ Etale π ∧ Surjective π ∧
      ∀ ⦃W' : Scheme.{u}⦄ (r : W' ⟶ W) (t : W' ⟶ Y'), r ≫ ι = t ≫ π →
        κ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} r) = 0 := by
  obtain ⟨φ, hφ⟩ := exists_spec_map_comp_fromSpecResidueField_eq g
  let : Algebra (S.residueField (genericPoint S)) K := φ.hom.toAlgebra
  let πL := f.fiberToSpecResidueField (genericPoint S)
  let i₀ := pullback.fst πL (Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField (genericPoint S)) K)))
  have hW₀ : IsPullback (i₀ ≫ f.fiberι (genericPoint S))
      (pullback.snd πL (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField (genericPoint S)) K)))) f g := by
    rw [← hφ]
    exact (IsPullback.of_hasPullback _ _).paste_horiz
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))
  let Φ := sq.isoIsPullback _ _ hW₀
  let ψ := Φ.inv
  let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod d))
  let FL := FirstFailureDiagram.constantZMod (f.fiber (genericPoint S)) d
  let α := ((etaleAbelianInverseImageConstantIso.{u, 0} ψ).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv
  let βi : (etaleAbelianInverseImage.{u, 0} ψ).obj A ≅
      (etaleAbelianInverseImage.{u, 0} i₀).obj FL :=
    (etaleAbelianInverseImage.{u, 0} ψ).mapIso eA ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} ψ).app M ≪≫
        ((etaleAbelianInverseImageConstantIso.{u, 0} i₀).app M).symm
  let κ₁ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i₀).obj FL) 1 :=
    (Ext.mk₀ α).comp ((κ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} ψ)).comp
      (Ext.mk₀ βi.hom) (add_zero 1)) (zero_add 1)
  have htors : ∀ (V : (f.fiber (genericPoint S)).Etale) (a : FL.obj.obj (op V)),
      ∃ n : ℕ, 0 < n ∧ (ringChar (S.residueField (genericPoint S)) = 0 ∨
        n.Coprime (ringChar (S.residueField (genericPoint S)))) ∧ n • a = 0 := fun V a =>
    ⟨d, hd, ringChar_eq_zero_or_coprime_of_isUnit (hdS _), by
      simpa only [natCast_zsmul] using
        FirstFailureDiagram.zsmul_constantZMod_eq_zero _ d (dvd_refl (d : ℤ)) V a⟩
  obtain ⟨ξ, hξ⟩ := (h03SC6 (S.residueField (genericPoint S)) K πL hdim FL htors 1).2 κ₁
  obtain ⟨Y', π, hfin, het, hsurj, hY'⟩ :=
    exists_finiteEtale_mapExactFunctor_eq_zero_of_fiber h0EZJ f σ hσ d hd hdS ξ
  refine ⟨Y', π, hfin, het, hsurj, fun W' r t hrt => ?_⟩
  let m := r ≫ Φ.hom
  have h1 := hY' (m ≫ i₀) t (by
    simp only [m, Category.assoc]
    rwa [sq.isoIsPullback_hom_fst _ _ hW₀])
  have h2 : κ₁.mapExactFunctor (etaleAbelianInverseImage.{u, 0} m) = 0 := by
    rw [← hξ]
    exact mapExactFunctor_etaleCohomologyRestrictionMap_eq_zero i₀ m FL ξ h1
  have h3 := mapExactFunctor_eq_zero_of_mk₀_comp_comp_mk₀ _ α βi.hom _ h2
  rwa [mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff,
    show m ≫ ψ = r by simp [m, ψ]] at h3

end Stacks.EtaleCohomology.SmoothBaseChange

end
