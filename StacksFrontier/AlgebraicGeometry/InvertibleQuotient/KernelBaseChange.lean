module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelTwist
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import Mathlib.RingTheory.PicardGroup

/-!
# Base change of the kernel of an invertible quotient, unconditionally

`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean` builds Tag 0B3V's comparison
`g^*(\ker q) ≅ \ker q'` for an invertible quotient `q : E ⟶ Q.L`, and reduces it — with no
hypothesis — to the single statement

`Mono ((Scheme.Modules.pullback g).map (kernel.ι Q.q))`

(`Stacks.Divisors.mono_quotientKernelBaseChangeMap_iff`), the canonical comparison being an
epimorphism always (`Stacks.Divisors.epi_quotientKernelBaseChangeMap`). This file proves that
statement, so the comparison and the left exactness of pullback on the kernel sequence of an
invertible quotient are available with no hypothesis.

The route is stalkwise and uses no local triviality of `Q.L`. Monomorphisms of sheaves of
modules are detected on stalks, on stalks `g^*` is base change along the germ map (Tag 0098),
and the stalk of an invertible sheaf of modules is an *invertible module* — hence projective —
so the stalk of the quotient is a split epimorphism, whose kernel an additive functor
preserves.

## Main results

* `Stacks.RingedSpace.smul_stalkObj_eq`: the `RingCat`-valued stalk action of the structure
  sheaf used by `AlgebraicGeometry.SheafOfModules.stalkObj` is the Tag 01CB action of
  `𝒪_{X,x}`, read through `Stacks.RingedSpace.ringStalkCommIso`. This is the one place the two
  spellings of the stalk of the structure sheaf meet.
* `Stacks.SheafOfModules.module_invertible_grpStalk_of_isInvertible`: **the stalk of an
  invertible sheaf of modules is an invertible module.** The stalk pairing of
  `Stacks.SheafOfModules.stalkPairing` is the witness; no locality of the stalk and no
  finiteness is used. Mathlib's `Module.Invertible` carries `Module.Projective` as an instance,
  which is all that is wanted below.
* `Stacks.SheafOfModules.isSplitEpi_stalkFunctor_map_of_isInvertible`: a surjection of sheaves
  of modules onto an invertible one splits at every stalk.
* `Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk`: module pullback
  keeps the kernel inclusion of a stalkwise-split surjection injective.
* `Stacks.Divisors.mono_pullback_map_kernel_ι`: **the residue of Tag 0B3V's kernel base-change
  clause, discharged.** Pullback of sheaves of modules carries `\ker Q.q ⟶ E` to a
  monomorphism, for every morphism of schemes and every invertible quotient.
* `Stacks.Divisors.preservesLimit_parallelPair_zero_pullback`: consequently pullback is left
  exact on the kernel sequence of an invertible quotient, which is the hypothesis
  `Stacks.Divisors.quotientKernelBaseChangeIso` takes.
* `Stacks.Divisors.quotientKernelBaseChange`: Tag 0B3V's quotient-kernel base-change
  comparison, with no hypothesis beyond the three comparison isomorphisms the tag itself
  supplies.

## Implementation notes

**Why no local triviality is needed.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean` propose proving the kernel
clause by trivializing `Q.L` on a cover, splitting there, and glueing, and record that the
glueing has no foothold. That route is not taken: an invertible module over *any* commutative
ring is projective (`Mathlib/RingTheory/PicardGroup.lean`), so the splitting is available at
each stalk directly from the stalk pairing, and no cover, no restriction of a pullback and no
glueing enters. `Stacks.Divisors.preservesLimit_parallelPair_zero_pullback_of_isSplitEpi` of
that file is the special case where the splitting is global.

**Two spellings of the stalk of the structure sheaf.** `AlgebraicGeometry.SheafOfModules.stalkObj`
puts the `RingCat`-valued stalk of `structureSheafRing` on the abelian-group stalk, while the whole
Tag 01CB stalk API — `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`,
`Stacks.SheafOfModules.stalkPairing` — is stated over the `CommRingCat`-valued
`Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk`. The abelian-group carriers coincide by
`rfl` and the rings are identified by `Stacks.RingedSpace.ringStalkCommIso`, so `smul_stalkObj_eq`
is the only crossing and everything else is read through it. Its statement needs the scalar
`let`-bound at the Tag 01CB spelling: a type *ascription* is a no-op here, and instance search for
the Tag 01CB action then fails on the `stalkObj` spelling of the carrier.

For the same reason the applications of `isSplitEpi_stalkFunctor_map_of_isInvertible` in
`mono_pullback_map_kernel_ι` pass their `Epi` and `IsInvertible` arguments explicitly:
`AlgebraicGeometry.Scheme.Modules` is a plain `def`, so its `Category` instance is a syntactically
different term and `Epi Q.q` is not found by synthesis at the
`SheafOfModules (structureSheafRing X.toRingedSpace)` spelling even with a proof of it in context.
The arguments are accepted when supplied, the two spellings being definitionally equal.

**Where the two `IsInvertible` classes meet.** `Stacks.Divisors.InvertibleQuotient.invertible`
is `AlgebraicGeometry.SheafOfModules.IsInvertible`, whereas the trivialization API of
`StacksDraft/AlgebraicGeometry/F3b/InvertibleTrivialization/` consumes
`Stacks.SheafOfModules.IsInvertible`. The crossing is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, used once, restating nothing.

**No tag is attached.** Tag 0B3V's base-change clause, the compatibility of the
conormal sheaf isomorphism with base change, also needs the bijection between sections and
invertible quotients and the conormal identification; this file supplies one of its inputs.
`Stacks.Divisors.quotientKernelBaseChange` is an untagged auxiliary `def` of that statement.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
universe u

namespace Stacks.RingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) (x : X.carrier)

/-- A `RingCat`-valued stalk element of the structure sheaf, read in the `CommRingCat`-valued
Tag 01CB stalk `𝒪_{X,x}` through `Stacks.RingedSpace.ringStalkCommIso`. -/
noncomputable abbrev toCommRingStalk
    (r : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x)) :
    ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) :=
  (ringStalkCommIso X x).hom.hom r

/-- **The two module structures on the stalk of a sheaf of modules agree.** The action of the
`RingCat`-valued stalk of the structure sheaf used by
`AlgebraicGeometry.SheafOfModules.stalkObj` is the Tag 01CB action of `𝒪_{X,x}`, read through
`Stacks.RingedSpace.ringStalkCommIso`.

Both actions are pinned by `germ (r • m) = germ r • germ m` and every element of either stalk
is a germ, so the identification is forced; `Stacks.RingedSpace.ringStalkCommIso_germ`
identifies the two germ maps of the structure sheaf. -/
lemma smul_stalkObj_eq (M : SheafOfModules.{u} (structureSheafRing X))
    (r : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x))
    (m : ToType (AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing X) x M)) :
    r • m =
      (let m' : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X M.val x) := m
       letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X M.val x
       toCommRingStalk X x r • m') := by
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X M.val x
  obtain ⟨U, hxU, a, ha⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := RingCat.{u}) (structureSheafRing X).obj r
  obtain ⟨V, hxV, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) M.val.presheaf m
  set W : Opens X.carrier := U ⊓ V with hW
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  set iU : W ⟶ U := homOfLE inf_le_left
  set iV : W ⟶ V := homOfLE inf_le_right
  set a' : ToType ((structureSheafRing X).obj.obj (op W)) :=
    ((structureSheafRing X).obj.map iU.op).hom a with ha'
  set t' : ToType (M.val.obj (op W)) := (M.val.presheaf.map iV.op).hom t with ht'
  have hra :
      (TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj W x hxW).hom a' = r := by
    rw [ha', TopCat.Presheaf.germ_res_apply]; exact ha
  have hmt :
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf W x hxW).hom t' = m := by
    rw [ht', TopCat.Presheaf.germ_res_apply]; exact ht
  let g : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X M.val x) :=
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf W x hxW).hom t'
  have e1 : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf W x hxW).hom
        (a' • t') =
      (TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj W x hxW).hom a' •
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf W x hxW).hom t' :=
    AlgebraicGeometry.SheafOfModules.germ_hom_smul (structureSheafRing X) x M.val W hxW a' t'
  have e2 : (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X M.val x W hxW) (a' • t') =
      Stacks.SheafOfModules.TensorStalkRingedSpace.ringGerm X x W hxW a' • g :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X M.val x W hxW a' t'
  have e3 : toCommRingStalk X x
      ((TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj W x hxW).hom a') =
      Stacks.SheafOfModules.TensorStalkRingedSpace.ringGerm X x W hxW a' :=
    ringStalkCommIso_germ X x W hxW a'
  rw [← hra, ← hmt]
  exact e1.symm.trans (e2.trans (congrArg
    (fun c : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) => c • g) e3.symm))

end Stacks.RingedSpace

namespace Stacks.SheafOfModules

/-- **The stalk of an invertible sheaf of modules is an invertible module.** A trivialization
`L ⊗_{𝒪_X} N ≅ 𝒪_X` (Tag 0B8K) gives the stalk pairing
`L_x ⊗_{𝒪_{X,x}} N_x ≃ₗ 𝒪_{X,x}` of `Stacks.SheafOfModules.stalkPairing`, which is exactly a
witness of `Module.Invertible`. No locality of the stalk and no finiteness is used. -/
theorem module_invertible_grpStalk_of_isInvertible
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing
      X).property L]
    (x : X.carrier) :
    letI := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X L.val x
    Module.Invertible (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x))
      (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X L.val x)) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing
      X).property) L).mp ‹_›
  exact .left (stalkPairing ψ x)


/-- **A surjection of sheaves of modules onto an invertible one splits at every stalk.** The
stalk `L_x` is an invertible `𝒪_{X,x}`-module
(`Stacks.SheafOfModules.module_invertible_grpStalk_of_isInvertible`), hence projective, and the
stalk functor preserves epimorphisms, so the surjection `E_x ⟶ L_x` admits a linear section. The
section is `𝒪_{X,x}`-linear and therefore linear for the `RingCat`-valued stalk action as well,
by `Stacks.RingedSpace.smul_stalkObj_eq`. -/
theorem isSplitEpi_stalkFunctor_map_of_isInvertible
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    {E L : SheafOfModules.{u} (structureSheafRing X)} (q : E ⟶ L) [Epi q]
    [IsInvertible X.presheaf (structureSheafRing
      X).property L]
    (x : X.carrier) :
    IsSplitEpi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).map q) := by
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X E.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X L.val x
  have := module_invertible_grpStalk_of_isInvertible X L x
  have hepi : Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).map q) :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).map_epi q
  have hsurj : Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X E.val
    L.val q.val x) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X E.val L.val q.val x) LinearMap.id
      hsurj
  refine IsSplitEpi.mk' ⟨ModuleCat.ofHom
    { toFun := s
      map_add' := fun a b => s.map_add a b
      map_smul' := fun r m => ?_ }, ?_⟩
  · exact (congrArg s (Stacks.RingedSpace.smul_stalkObj_eq X x L r m)).trans
      ((s.map_smul (Stacks.RingedSpace.toCommRingStalk X x r) m).trans
        (Stacks.RingedSpace.smul_stalkObj_eq X x E r (s m)).symm)
  · ext m
    exact LinearMap.congr_fun hs m

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

/-- **Module pullback keeps the kernel inclusion of a stalkwise-split surjection injective.**
Monomorphisms of sheaves of modules are detected on stalks
(`AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono`), on stalks `f^*` is the stalk at `f x`
followed by base change along the germ map (Stacks 0098,
`Stacks.RingedSpace.stalkModulePullbackFunctorIso`), the stalk functor preserves finite limits,
and base change — being additive — preserves the kernel of a split epimorphism
(`Stacks.preservesLimit_parallelPair_zero_of_isSplitEpi`). So the composite preserves the
kernel of `q`, and the image of `kernel.ι q` factors as an isomorphism followed by a kernel
inclusion. -/
theorem mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
    {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {E L : SheafOfModules.{u} (structureSheafRing Y)} (q : E ⟶ L)
    (hsplit : ∀ x : X.carrier,
      IsSplitEpi ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        (f.hom.base x)).map q)) :
    Mono ((modulePullback f).map (kernel.ι q)) := by
  apply AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono
  intro x
  refine (Stacks.mono_iff_of_isIso_sq
      ((stalkModulePullbackFunctorIso f x).hom.app (kernel q))
      ((stalkModulePullbackFunctorIso f x).hom.app E)
      ((stalkModulePullbackFunctorIso f x).hom.naturality (kernel.ι q))).mpr ?_
  have := hsplit x
  set SY := AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) (f.hom.base x)
    with hSY
  set BC := stalkBaseChange f x with hBC
  change Mono (BC.map (SY.map (kernel.ι q)))
  rw [← kernelComparison_comp_ι q SY, BC.map_comp]
  have : PreservesLimit (parallelPair (SY.map q) 0) BC :=
    Stacks.preservesLimit_parallelPair_zero_of_isSplitEpi BC (SY.map q)
  rw [← kernelComparison_comp_ι (SY.map q) BC]
  infer_instance

end Stacks.RingedSpace

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **Pullback of sheaves of modules keeps the kernel inclusion of an invertible quotient
injective, with no hypothesis.** The quotient `q : E ⟶ L` is surjective onto an invertible `L`,
so at every stalk it is a surjection onto an invertible — hence projective — module, which
splits; and a module pullback keeps the kernel inclusion of a stalkwise-split surjection
injective. -/
theorem mono_pullback_map_kernel_ι (E : X.Modules) (Q : InvertibleQuotient X E) :
    Mono ((Scheme.Modules.pullback g).map (kernel.ι Q.q)) := by
  have hq : Epi Q.q := Q.epi
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Q.L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr Q.invertible
  exact Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
    g.toLRSHom.toShHom Q.q
    fun y => @Stacks.SheafOfModules.isSplitEpi_stalkFunctor_map_of_isInvertible
      X.toRingedSpace E Q.L Q.q hq hinv _


/-- **Pullback of sheaves of modules is left exact on the kernel sequence of an invertible
quotient, with no hypothesis at all.** For an epimorphism, left exactness on its kernel sequence
is exactly injectivity of the kernel comparison
(`Stacks.preservesLimit_parallelPair_zero_of_mono_kernelComparison`), and the comparison composed
with the kernel inclusion is the pullback of `kernel.ι Q.q`, which is injective by
`Stacks.Divisors.mono_pullback_map_kernel_ι`.

This discharges the hypothesis of `Stacks.Divisors.quotientKernelBaseChangeIso`. -/
theorem preservesLimit_parallelPair_zero_pullback (E : X.Modules) (Q : InvertibleQuotient X E) :
    PreservesLimit (parallelPair Q.q 0) (Scheme.Modules.pullback g) := by
  have hq : Epi Q.q := Q.epi
  have h : Mono (kernelComparison Q.q (Scheme.Modules.pullback g) ≫
      kernel.ι ((Scheme.Modules.pullback g).map Q.q)) := by
    rw [kernelComparison_comp_ι]
    exact mono_pullback_map_kernel_ι g E Q
  exact Stacks.preservesLimit_parallelPair_zero_of_mono_kernelComparison
    (Scheme.Modules.pullback g) Q.q (mono_of_mono _ (kernel.ι _))

/-- **Tag 0B3V's comparison of the pullback of a quotient kernel with the kernel of the
pulled-back quotient, with no hypothesis beyond the three comparison isomorphisms.** This is
`Stacks.Divisors.quotientKernelBaseChangeIsoOfMono` with its hypothesis discharged by
`Stacks.Divisors.mono_pullback_map_kernel_ι`; the comparison is the canonical
`Stacks.Divisors.quotientKernelBaseChangeMap`, by
`Stacks.Divisors.eq_quotientKernelBaseChangeMap`. -/
noncomputable def quotientKernelBaseChange
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    { e : (Scheme.Modules.pullback g).obj (kernel Q.q) ≅ kernel Q'.q //
      e.hom ≫ kernel.ι Q'.q =
        (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv } :=
  quotientKernelBaseChangeIsoOfMono g E E' hE Q Q' hL hq
    ((mono_quotientKernelBaseChangeMap_iff g E E' hE Q Q' hL hq).mpr
      (mono_pullback_map_kernel_ι g E Q))

end Stacks.Divisors

end
