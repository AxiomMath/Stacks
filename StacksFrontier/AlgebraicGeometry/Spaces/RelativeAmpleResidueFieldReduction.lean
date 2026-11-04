module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocus

/-!
# Ampleness over a field-valued point descends to the residue field

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `L`
be an `𝒪_X`-module, let `U` be a scheme of the site with a morphism `b : h_U ⟶ Y`, and let `r`
be a field-valued point of `U`, with field `K` and underlying point `u` of `U`. If the pullback
of `L` is ample over the base change of `f` along `Spec K ⟶ U ⟶ Y`, then it is ample over the
base change of `f` along `Spec κ(u) ⟶ U ⟶ Y`. This is the reduction "by Lemma 0D3C we may
assume that `k = κ(y)`" of the proof of Stacks 0D3D: `Spec K ⟶ Spec κ(u)` is a one-member fpqc
covering, and Stacks 0D3C, (2) implies (1), descends ampleness along it.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_yoneda_map_of_flat_of_surjective`: a flat surjective
  morphism of affine schemes of the site is a one-member fpqc covering of algebraic spaces.
* `AlgebraicGeometry.Space.residueFieldLift`: the morphism `Spec K ⟶ Spec κ(u)` of the site
  through which a field-valued point `r` of `U` factors, `u` being the point of `U` under `r`.
* `AlgebraicGeometry.Space.isRelativelyAmple_residueField_of_fieldValuedPoint`: the reduction
  itself, granted the fpqc case of Stacks 0D3C in the form
  `AlgebraicGeometry.Space.RelativeAmpleFpqcDescends`.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A flat surjective morphism of affine schemes of the site is a one-member fpqc covering of
algebraic spaces (Stacks 03MQ): the refinement clause at an affine test object `T` is the base
change of the morphism to `T`, a flat surjective morphism of affine schemes. -/
theorem isFpqcCovering_yoneda_map_of_flat_of_surjective {U V : BigFppfOver B S hS} (b : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hf : Flat ((BigFppfOver.toScheme B S hS).map b))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map b)) :
    IsFpqcCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.map b) := by
  let G := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  refine ⟨fun _ => isFlat_yoneda_map B S hS b hf, fun T g => ?_⟩
  let h : A.obj T ⟶ V := yoneda.preimage g
  have hg : yoneda.map h = g := yoneda.map_preimage _
  have sq := (IsPullback.of_hasPullback h b).map G
  have : IsAffine (G.obj U) := hU
  have : IsAffine (G.obj V) := hV
  have : IsAffine (G.obj (A.obj T)) := T.property
  have hW : IsAffine (G.obj (pullback h b)) := IsAffine.of_isIso sq.isoPullback.hom
  let W : BigAffineFppf B S hS := ⟨pullback h b, hW⟩
  let q : W ⟶ T := ObjectProperty.homMk (pullback.fst h b)
  let E : PreZeroHypercover.{u + 1} T := .singleton q
  refine ⟨E, inferInstance, ?_, ?_⟩
  · have : Flat (G.map (pullback.fst h b)) := MorphismProperty.of_isPullback sq.flip hf
    have : Surjective (G.map (pullback.fst h b)) := MorphismProperty.of_isPullback sq.flip hs
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    exact (G.map (pullback.fst h b)).singleton_mem_fpqcPrecoverage
  · intro j
    refine ⟨PUnit.unit, yoneda.map (pullback.snd h b), ?_⟩
    show yoneda.map (pullback.snd h b) ≫ yoneda.map b = yoneda.map (pullback.fst h b) ≫ g
    rw [← hg, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- The residue-field morphism of the point under a field-valued point: for a field-valued
point `r` of the scheme `U` of the site, with field `K`, the morphism of field spectra
`Spec K ⟶ Spec κ(u)` of the site, `u` being `AlgebraicGeometry.Space.schemePoint` of `r`, through
which `r` factors (`AlgebraicGeometry.Space.residueFieldLift_comp`). -/
def residueFieldLift (U : BigFppfOver B S hS) (r : FieldValuedPoint B S hS (yoneda.obj U)) :
    r.siteObject ⟶ residueFieldObject B S hS U (schemePoint B S hS U r)
      (B.residueField_spec_contains U.left.property (schemePoint B S hS U r)) :=
  Over.homMk ⟨Spec.map (Scheme.SpecToEquivOfField r.carrier U.left.1
      ((BigFppfOver.toScheme B S hS).map r.value)).2⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map (Scheme.SpecToEquivOfField r.carrier U.left.1
        ((BigFppfOver.toScheme B S hS).map r.value)).2 ≫
      (U.left.1.fromSpecResidueField _ ≫ U.hom.1) = r.toBase
    rw [← Category.assoc]
    exact (congrArg (· ≫ U.hom.1) ((Scheme.SpecToEquivOfField r.carrier U.left.1).left_inv
      ((BigFppfOver.toScheme B S hS).map r.value))).trans
      (congrArg (fun k => k.1) (Over.w r.value)))

/-- A field-valued point of `U` factors through the residue field of its point. -/
theorem residueFieldLift_comp (U : BigFppfOver B S hS)
    (r : FieldValuedPoint B S hS (yoneda.obj U)) :
    residueFieldLift U r ≫ residueFieldMap B S hS U (schemePoint B S hS U r)
        (B.residueField_spec_contains U.left.property (schemePoint B S hS U r)) = r.value := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (Scheme.SpecToEquivOfField r.carrier U.left.1).left_inv
    ((BigFppfOver.toScheme B S hS).map r.value)

/-- The residue-field morphism of a field-valued point is a one-member fpqc covering: it is a
morphism of spectra of fields, flat and surjective. -/
theorem isFpqcCovering_residueFieldLift (U : BigFppfOver B S hS)
    (r : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsFpqcCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.map (residueFieldLift U r)) := by
  refine isFpqcCovering_yoneda_map_of_flat_of_surjective _
    (inferInstanceAs (IsAffine (Spec (.of r.carrier))))
    (inferInstanceAs (IsAffine (Spec (.of (U.left.1.residueField (schemePoint B S hS U r))))))
    (inferInstanceAs (Flat (Spec.map (Scheme.SpecToEquivOfField r.carrier U.left.1
      ((BigFppfOver.toScheme B S hS).map r.value)).2))) ?_
  show Surjective (Spec.map (Scheme.SpecToEquivOfField r.carrier U.left.1
    ((BigFppfOver.toScheme B S hS).map r.value)).2)
  exact ⟨fun _ => ⟨IsLocalRing.closedPoint r.carrier, Subsingleton.elim _ _⟩⟩

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)

/-- **Ampleness over a field-valued point descends to the residue field.** Let
`b : h_U ⟶ Y` be a morphism from a scheme of the site and `r` a field-valued point of `U`, with
field `K` and underlying point `u`. If the pullback of `L` is ample on a base change of `f`
along `Spec K ⟶ U ⟶ Y`, then it is ample on every base change of `f` along
`Spec κ(u) ⟶ U ⟶ Y`.

The given base change over `Spec K` is the base change of the one over `Spec κ(u)` along
`Spec K ⟶ Spec κ(u)` (pasting), which is a one-member fpqc covering; Stacks 0D3C, (2) implies
(1), concludes. -/
theorem isRelativelyAmple_residueField_of_fieldValuedPoint
    (hdesc : RelativeAmpleFpqcDescends B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ Y.1) (r : FieldValuedPoint B S hS (yoneda.obj U))
    {X'' : AlgebraicSpaces B S hS} (p'' : X'' ⟶ X)
    (f'' : X'' ⟶ representedAlgebraicSpace B S hS r.siteObject)
    (hsq : IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ b)))
    (hamp : IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L))
    {X' : AlgebraicSpaces B S hS} (p' : X' ⟶ X)
    (f' : X' ⟶ representedAlgebraicSpace B S hS (residueFieldObject B S hS U
      (schemePoint B S hS U r)
      (B.residueField_spec_contains U.left.property (schemePoint B S hS U r))))
    (hsq' : IsPullback p' f' f (ObjectProperty.homMk (yoneda.map (residueFieldMap B S hS U
      (schemePoint B S hS U r)
      (B.residueField_spec_contains U.left.property (schemePoint B S hS U r))) ≫ b))) :
    IsRelativelyAmple B S hS f' ((modulePullback B S hS p').obj L) := by
  let c : representedAlgebraicSpace B S hS r.siteObject ⟶
      representedAlgebraicSpace B S hS (residueFieldObject B S hS U (schemePoint B S hS U r)
        (B.residueField_spec_contains U.left.property (schemePoint B S hS U r))) :=
    ObjectProperty.homMk (yoneda.map (residueFieldLift U r))
  have hc : c ≫ ObjectProperty.homMk (yoneda.map (residueFieldMap B S hS U
      (schemePoint B S hS U r)
      (B.residueField_spec_contains U.left.property (schemePoint B S hS U r))) ≫ b) =
      (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ b) :
        representedAlgebraicSpace B S hS r.siteObject ⟶ Y) := by
    ext1
    show yoneda.map (residueFieldLift U r) ≫ yoneda.map (residueFieldMap B S hS U _ _) ≫ b =
      yonedaEquiv.symm r.value ≫ b
    rw [← Category.assoc, ← Functor.map_comp, residueFieldLift_comp]
    rfl
  -- the given square over `Spec K` is the base change of the square over `Spec κ(u)`
  let pc : X'' ⟶ X' := hsq'.lift p'' (f'' ≫ c) (by rw [Category.assoc, hc, hsq.w])
  have hpc : pc ≫ p' = p'' := hsq'.lift_fst _ _ _
  have hfc : pc ≫ f' = f'' ≫ c := hsq'.lift_snd _ _ _
  have hbig : IsPullback (pc ≫ p') f'' f (c ≫ ObjectProperty.homMk
      (yoneda.map (residueFieldMap B S hS U (schemePoint B S hS U r)
        (B.residueField_spec_contains U.left.property (schemePoint B S hS U r))) ≫ b)) := by
    rwa [hpc, hc]
  have hsqc : IsPullback pc f'' f' c := IsPullback.of_right hbig hfc hsq'
  refine hdesc f' _ (Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS p') (L := L) (hL := hL))
    (fun _ : PUnit.{u + 2} => hsqc) (isFpqcCovering_residueFieldLift U r)
    fun _ => (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS pc p').app L)).mpr ?_
  rwa [hpc]

end AlgebraicGeometry.Space

end
