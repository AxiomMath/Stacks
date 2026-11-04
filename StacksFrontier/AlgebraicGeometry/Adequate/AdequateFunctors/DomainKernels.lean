module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCokernelToExtension
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteFreeLift
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels

/-!
# Tag 06V3 on a restricted domain of algebras

[Stacks, Tag 06V3] — adequate module-valued functors are closed under kernels — is proved for
the full domain of commutative `A`-algebras as `AdequateFunctor.isAdequate_kernel`. This file
carries it to a domain `ι : C ⥤ CommAlgCat A` with a base algebra object on which the lifting
property of [Stacks, Tag 06V0] holds, and then to the algebras of a site, where both inputs are
available.

The proof of `AdequateFunctor.isAdequate_kernel` goes through: the two kernel presentations
`a : M₁ ⟶ N₁` and `b : M₂ ⟶ N₂` give monos `F ↪ E M₁` and `G ↪ E M₂`, whose graph
`j = ⟨uF, φ uG⟩ : F ↪ E (M₁ ⊞ M₂)` is a mono into a module extension; `Ker φ` is then the kernel of
`E (⟨κ, pr₂⟩)` for `κ : M₁ ⊞ M₂ ⟶ K` the map of modules underlying `E (M₁ ⊞ M₂) ↠ Coker j ↪ E K`,
where `K` comes from a kernel presentation of `Coker j`.

The one step of that argument not generic is the adequacy of `Coker j`. In that proof it is
[Stacks, Tag 06V2]; but the target of `j` is a module extension, so [Stacks, Tag 06V1] suffices,
and on a restricted domain that is `AdequateFunctor.isAdequate_cokernel_to_moduleExtension_on`. The
other non-generic step is reading `κ` off from a morphism of module extensions, which is fullness
of extension of scalars on the domain, `AdequateFunctor.full_moduleExtensionFunctorOn`.

## Main results

* `AdequateFunctor.isAdequate_kernel_on` — [Stacks, Tag 06V3] on a restricted domain of
  algebras, given a base algebra object and the lifting property of [Stacks, Tag 06V0] there.
* `AdequateFunctor.finiteFreeKernelLifting_site` — that lifting property over the algebras of a
  site.
* `AdequateFunctor.isAdequate_kernel_site` — [Stacks, Tag 06V3] over the algebras of a site.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06V3 is
`AdequateFunctor.isAdequate_kernel`, over all commutative algebras, and these are that statement
transported to a restricted domain.

`AdequateFunctor.isAdequate_kernel_of_isLinearlyAdequate_site` is the special case of
`AdequateFunctor.isAdequate_kernel_site` in which the source is *linearly* adequate. It is not
subsumed as a proof: it needs no 06V1 at all, reducing instead to
`AdequateFunctor.isAdequate_kernel_of_moduleExtensionLift` with 06V0 discharging its one
hypothesis directly, and so is the shorter route when the source is linearly adequate.

The values of the functors are taken in a universe already containing the ring and algebra
universes, which is where the geometric applications put them, so the universe lift of
`AdequateFunctor.IsKernelPresentation` is erased by `AdequateFunctor.presheafOfModulesUliftIso`
rather than carried along; that is what removes the `uliftKernelIso` step of the proof of
`AdequateFunctor.isAdequate_kernel`.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06V1](https://stacks.math.columbia.edu/tag/06V1)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u u₁ v₁

namespace AdequateFunctor

section Domain

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]

/-- **Stacks Lemma 06V3 on a restricted domain of algebras.** The kernel of a morphism of
adequate module-valued functors on a domain of algebras is adequate, given a base algebra
object and the lifting property of [Stacks, Tag 06V0] on that domain.

The graph of the morphism is a mono from the source into the module extension of the biproduct
of the two presenting modules, so [Stacks, Tag 06V1] on the domain makes its cokernel adequate;
a kernel presentation of that cokernel together with fullness of extension of scalars produces
the map of modules presenting the kernel. -/
public theorem isAdequate_kernel_on {ι : C ⥤ CommAlgCat.{max u v} A} (b : BaseAlgebraObject.{v} ι)
    (hlift : FiniteFreeKernelLifting.{w, v} ι)
    {F G : ModuleValuedFunctorOn.{max u v w, v} ι} (φ : F ⟶ G)
    (hF : IsAdequate.{max u v w, v} ι F) (hG : IsAdequate.{max u v w, v} ι G) :
    IsAdequate.{max u v w, v} ι (kernel φ) := by
  classical
  let R := algebraRingDiagramOn.{v} ι
  let E := moduleExtensionFunctorOn.{max u v w, v} ι
  obtain ⟨M₁, N₁, a, ⟨eF₀⟩⟩ := hF
  obtain ⟨M₂, N₂, bb, ⟨eG₀⟩⟩ := hG
  have hFad : IsAdequate.{max u v w, v} ι F := ⟨M₁, N₁, a, ⟨eF₀⟩⟩
  let αF : F ≅ kernel (E.map a) :=
    (presheafOfModulesUliftIso.{max u v, max u v w} R F).symm ≪≫ eF₀
  let αG : G ≅ kernel (E.map bb) :=
    (presheafOfModulesUliftIso.{max u v, max u v w} R G).symm ≪≫ eG₀
  let uF : F ⟶ E.obj M₁ := αF.hom ≫ kernel.ι (E.map a)
  let uG : G ⟶ E.obj M₂ := αG.hom ≫ kernel.ι (E.map bb)
  let P := M₁ ⊞ M₂
  let eP := Functor.mapBiprod E M₁ M₂
  let graph : F ⟶ E.obj M₁ ⊞ E.obj M₂ := biprod.lift uF (φ ≫ uG)
  let j : F ⟶ E.obj P := graph ≫ eP.inv
  have eP_fst : eP.hom ≫ biprod.fst = E.map biprod.fst := by
    show (Functor.mapBiprod E M₁ M₂).hom ≫ biprod.fst = E.map biprod.fst
    rw [Functor.mapBiprod_hom]
    simp
  have eP_snd : eP.hom ≫ biprod.snd = E.map biprod.snd := by
    show (Functor.mapBiprod E M₁ M₂).hom ≫ biprod.snd = E.map biprod.snd
    rw [Functor.mapBiprod_hom]
    simp
  have eP_inv_fst : eP.inv ≫ E.map biprod.fst = biprod.fst := by
    calc
      eP.inv ≫ E.map biprod.fst = eP.inv ≫ (eP.hom ≫ biprod.fst) := by rw [eP_fst]
      _ = biprod.fst := by simp []
  have eP_inv_snd : eP.inv ≫ E.map biprod.snd = biprod.snd := by
    calc
      eP.inv ≫ E.map biprod.snd = eP.inv ≫ (eP.hom ≫ biprod.snd) := by rw [eP_snd]
      _ = biprod.snd := by simp []
  have hj_fst : j ≫ E.map biprod.fst = uF := by
    dsimp [j, graph]
    rw [Category.assoc, eP_inv_fst]
    simp
  have hj_snd : j ≫ E.map biprod.snd = φ ≫ uG := by
    dsimp [j, graph]
    rw [Category.assoc, eP_inv_snd]
    simp
  have : Mono uF := inferInstance
  have : Mono uG := inferInstance
  have : Mono j := by
    refine ⟨?_⟩
    intro X x y hxy
    have hh := congrArg (fun q => q ≫ E.map biprod.fst) hxy
    have hu : x ≫ uF = y ≫ uF := by
      rw [← hj_fst]
      simpa only [Category.assoc] using hh
    exact (cancel_mono uF).1 hu
  let cokerCofork := CokernelCofork.ofπ (cokernel.π j) (cokernel.condition j)
  let hJ : IsLimit (KernelFork.ofι j (CokernelCofork.condition cokerCofork)) :=
    Abelian.monoIsKernelOfCokernel cokerCofork (cokernelIsCokernel j)
  have hP : IsAdequate.{max u v w, v} ι (E.obj P) :=
    IsAdequate.restrictDomain ι (𝟭 _) _ (isAdequate_moduleExtension (A := A) P)
  let hQ := isAdequate_cokernel_to_moduleExtension_on b hlift F P j hFad
  obtain ⟨K, T, k, ⟨eQ⟩⟩ := hQ
  let qLift := presheafOfModulesUliftIso.{max u v, max u v w} R (cokernel j)
  let m : cokernel j ⟶ E.obj K := qLift.inv ≫ eQ.hom ≫ kernel.ι (E.map k)
  have : Mono m := inferInstanceAs (Mono (qLift.inv ≫ eQ.hom ≫ kernel.ι (E.map k)))
  let t : E.obj P ⟶ E.obj K := cokernel.π j ≫ m
  have hT : IsLimit (KernelFork.ofι j (show j ≫ t = 0 by simp [t])) :=
    isKernelCompMono hJ m rfl
  let κ : P ⟶ K := moduleHomOfExtensionNatTransOn b t
  have hκ : E.map κ = t := (moduleExtension_natTransOn_eq_map b t).symm
  let H : P ⟶ K ⊞ M₂ := biprod.lift κ biprod.snd
  let eH := Functor.mapBiprod E K M₂
  let j₂ : E.obj P ⟶ E.obj K ⊞ E.obj M₂ := biprod.lift t (E.map biprod.snd)
  have hE : E.map H ≫ eH.hom = j₂ := by
    simpa [eH, H, j₂, hκ] using (biprod.map_lift_mapBiprod E K M₂ κ biprod.snd)
  let η : kernel φ ⟶ E.obj P := kernel.ι φ ≫ j
  have hη : η ≫ j₂ = 0 := by
    apply biprod.hom_ext
    · simp [η, j₂, Category.assoc, t]
    · simp [η, j₂, Category.assoc, hj_snd]
  have hs₁ (s : Fork j₂ 0) : s.ι ≫ t = 0 := by
    rw [show t = j₂ ≫ biprod.fst by simp [j₂], ← Category.assoc, KernelFork.condition, zero_comp]
  have hs₂ (s : Fork j₂ 0) : s.ι ≫ E.map biprod.snd = 0 := by
    rw [show E.map biprod.snd = j₂ ≫ biprod.snd by simp [j₂], ← Category.assoc,
      KernelFork.condition, zero_comp]
  let factorToF (s : Fork j₂ 0) : s.pt ⟶ F := hT.lift (KernelFork.ofι s.ι (hs₁ s))
  have factorToF_comp (s : Fork j₂ 0) : factorToF s ≫ j = s.ι := Fork.IsLimit.lift_ι hT
  have factorToF_phi (s : Fork j₂ 0) : factorToF s ≫ φ = 0 :=
    (cancel_mono uG).1 (by
      rw [Category.assoc, ← hj_snd, ← Category.assoc, factorToF_comp, hs₂, zero_comp])
  let liftPair (s : Fork j₂ 0) : s.pt ⟶ kernel φ :=
    kernel.lift φ (factorToF s) (factorToF_phi s)
  have liftPair_comp (s : Fork j₂ 0) : liftPair s ≫ η = s.ι := by
    simp [liftPair, η, factorToF_comp]
  have hPair : IsLimit (KernelFork.ofι η hη) := by
    refine Fork.IsLimit.mk _ liftPair (fun s => liftPair_comp s) ?_
    intro s x hx
    apply (cancel_mono (kernel.ι φ)).1
    apply (cancel_mono j).1
    calc
      x ≫ kernel.ι φ ≫ j = s.ι := by simpa [η, Category.assoc] using hx
      _ = liftPair s ≫ kernel.ι φ ≫ j := by
        symm
        simpa [η, Category.assoc] using liftPair_comp s
  let hFinal := IsKernel.ofCompIso (f := j₂) (l := E.map H) eH hE hPair
  refine ⟨P, K ⊞ M₂, H, ⟨?_⟩⟩
  exact presheafOfModulesUliftIso.{max u v, max u v w} R (kernel φ) ≪≫
    hFinal.conePointUniqueUpToIso (limit.isLimit (parallelPair (E.map H) 0))

end Domain

/-! ### Tag 06V3 over the algebras of a site -/

section Site

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- The lifting property of [Stacks, Tag 06V0] holds over the algebras of a site whose cutoff is
an uncountable strong prelimit, by
`AdequateFunctor.exists_lift_from_finite_free_kernel_site`. -/
public theorem finiteFreeKernelLifting_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ) :
    FiniteFreeKernelLifting.{w, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) := by
  intro M n m L i d φ hmono hd hexact
  have := hmono
  exact exists_lift_from_finite_free_kernel_site.{max u w} hκ hsl A
    (M := (M : Type (max u w))) hA n m L i d φ hd hexact

include hκ hsl in
/-- **Stacks Lemma 06V3 over the algebras of a site.** The kernel of a morphism of adequate
module-valued functors on the algebras whose spectra have size below the cutoff is adequate.

The two inputs of `AdequateFunctor.isAdequate_kernel_on` are the base ring as an object of the
site, `AdequateFunctor.BaseAlgebraObject.siteOfSpecMem`, and the lifting property above. -/
public theorem isAdequate_kernel_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    {F G : ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))}
    (φ : F ⟶ G)
    (hF : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) F)
    (hG : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) G) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (kernel φ) :=
  isAdequate_kernel_on.{w, u} (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
    (finiteFreeKernelLifting_site.{w} hκ hsl A hA) φ hF hG

end Site

end AdequateFunctor

end
