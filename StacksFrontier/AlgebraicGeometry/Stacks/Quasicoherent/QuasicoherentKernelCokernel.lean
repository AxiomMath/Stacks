module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentRightExact

/-!
# Kernels and cokernels of maps of quasi-coherent modules (Stacks 0GQL)

Let `𝒳` be an algebraic stack.  The category `QCoh(𝒪_𝒳)` is abelian and the inclusion functor
`i : QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact but not exact in general (**Stacks 06WV**).
**Stacks 0GQL** uses the coherator `Q` of **Stacks 0778** and **Stacks 0779** to say precisely
how far from exact it is: for a map `φ : 𝓕 → 𝓖` of quasi-coherent `𝒪_𝒳`-modules,

1. `Coker(φ)` computed in `Mod(𝒪_𝒳)` is quasi-coherent and is the cokernel of `φ` in
   `QCoh(𝒪_𝒳)`;
2. `Im(φ)` computed in `Mod(𝒪_𝒳)` is quasi-coherent and is the image of `φ` in `QCoh(𝒪_𝒳)`;
3. `Ker(φ)` computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` by **Stacks 0771**, and
   `Q(Ker(φ))` is the kernel of `φ` in `QCoh(𝒪_𝒳)`.

Clause (1) and the second half of clause (3) are proved here, and both are formal consequences
of the two structural facts the remark quotes:

* `i` preserves colimits (**Stacks 06WN** part (1), which is how the source gets right exactness
  in **Stacks 06WV** part (3)), so it carries the cokernel of `φ` in `QCoh(𝒪_𝒳)` to a cokernel of
  `i φ`; the cokernel computed in `Mod(𝒪_𝒳)` is therefore `i` of a quasi-coherent module, which
  is both halves of clause (1);
* `Q` is a right adjoint (**Stacks 0778**), so it preserves kernels, and the composite `Q ∘ i` is
  the identity because the inclusion is fully faithful; transporting the kernel of `Q(i φ)` along
  that identification gives the kernel of `φ` in `QCoh(𝒪_𝒳)`, which is the second half of
  clause (3).

## Main results

* `AlgebraicGeometry.FibredSite.isColimitCokernelCoforkMapQuasicoherentInclusion` and
  `AlgebraicGeometry.FibredSite.isQuasicoherent_cokernel_quasicoherentInclusion`:
  **Stacks 0GQL** part (1).
* `AlgebraicGeometry.Stack.isLimitKernelForkFlatBaseChangeQuasicoherator`:
  **Stacks 0GQL** part (3), second half.

## Implementation notes

The right exactness of `i` that clause (1) rests on is
`AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion`, and the finite
colimits it preserves are `AlgebraicGeometry.FibredSite.hasFiniteColimits_quasicoherentModules`;
both hold over the closure of quasi-coherence under colimits, the standing hypothesis `hclosed`
of this neighbourhood, and they are taken here as instance arguments so that the statements can
speak of `cokernel φ` at all.  They are registered as the right-exactness clause of
**Stacks 0GQL** by `add_to_stacks` below.

Clause (3) is split by the source itself, and only its second half is available.  Its first half
— that `Ker(φ)` computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` — is **Stacks 0771** part (2),
the weak Serre subcategory property, which this library does not have; the second half is stated
over the existence of that kernel inside `LQCoh^fbc(𝒪_𝒳)`, as the instance argument
`HasKernel ((quasicoherentToFlatBaseChange …).map φ)`, and nothing else about it is assumed.

The identification `Q ∘ i ≅ 𝟭` is used in the form
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoheratorCompInclusionIsoId`, so that no
invertibility instance has to be arranged for the unit of the adjunction before the statements
can be written down.

Clause (2) and the abelianness of `QCoh(𝒪_𝒳)` are not here.  Abelianness is **Stacks 06WV**
part (2), which the source derives from the equivalence `QCoh(𝒪_𝒳) ≅ QCoh(U, R, s, t, c)` of
**Stacks 06WV** part (1); that equivalence is not in the library, and the library carries
`Abelian (QCoh(𝒪_𝒳))` as a hypothesis wherever it needs it.  Clause (2) needs more than the
adjunction: a monomorphism of `QCoh(𝒪_𝒳)` need not be a monomorphism of `Mod(𝒪_𝒳)` — its kernel
there is only parasitic — so identifying `Im(φ)` with the image in `QCoh(𝒪_𝒳)` needs the fact
that a parasitic subsheaf of a module sheaf vanishes, that is, that every object of `𝒳` is
covered by flat objects.  The non-exactness of `i` asserted in the preamble is the second half of
**Stacks 06WV** part (3), whose only proof is the counterexample of Descent, Lemma 35.10.2.

## References

* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

add_to_stacks 0GQL "the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) is right exact, over the closure of \
  quasi-coherence under colimits" preservesFiniteColimits_quasicoherentInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [HasFiniteColimits (quasicoherentModules.{u, u + 1, u, u} B S hS p hp)]
  [PreservesFiniteColimits
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι]

/-- **Stacks 0GQL, part (1).**  Let `φ : 𝓕 → 𝓖` be a map of quasi-coherent `𝒪_𝒳`-modules.  The
cokernel of `φ` in `QCoh(𝒪_𝒳)`, included into `Mod(𝒪_𝒳)` together with its projection, is a
cokernel of `φ` in `Mod(𝒪_𝒳)`.

So the cokernel computed in `Mod(𝒪_𝒳)` is the image of a quasi-coherent module — which is the
quasi-coherence half of the clause, recorded separately as
`AlgebraicGeometry.FibredSite.isQuasicoherent_cokernel_quasicoherentInclusion` — and it is the
cokernel in `QCoh(𝒪_𝒳)`.  The proof is the right exactness of the inclusion, which is how the
source gets the clause. -/
@[stacks 0GQL "part (1): the cokernel of a map of quasi-coherent modules computed in Mod(𝒪_𝒳) is \
  the inclusion of the cokernel computed in QCoh(𝒪_𝒳), over the closure of quasi-coherence under \
  colimits"]
def isColimitCokernelCoforkMapQuasicoherentInclusion
    {F G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp} (φ : F ⟶ G) :
    IsColimit (Cofork.ofπ
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringStructureSheafCore B S hS p hp .fppf)).ι.map (cokernel.π φ))
      (by simp only [← Functor.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
      Cofork ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι.map φ) 0) :=
  isColimitOfHasCokernelOfPreservesColimit _ _

/-- **Stacks 0GQL, part (1), the quasi-coherence half.**  The cokernel of a map of quasi-coherent
`𝒪_𝒳`-modules computed in `Mod(𝒪_𝒳)` is quasi-coherent, because it is isomorphic to the
inclusion of the cokernel computed in `QCoh(𝒪_𝒳)`. -/
@[stacks 0GQL "part (1), the quasi-coherence half: the cokernel computed in Mod(𝒪_𝒳) of a map of \
  quasi-coherent modules is quasi-coherent, over the closure of quasi-coherence under colimits"]
theorem isQuasicoherent_cokernel_quasicoherentInclusion
    {F G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp} (φ : F ⟶ G) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf))
      (cokernel ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι.map φ)) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).prop_of_iso
    (PreservesCokernel.iso _ φ) (cokernel φ).property

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS p hp hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))
  (hlsD : LocallySmall.{u}
    (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp))

/-- The map `Q(Ker(i φ)) ⟶ 𝓕` of **Stacks 0GQL** part (3): apply the coherator to the inclusion
of the kernel of `i φ` inside `LQCoh^fbc(𝒪_𝒳)`, then use the identification `Q ∘ i ≅ 𝟭` of
**Stacks 0778** at `𝓕`. -/
def quasicoheratorKernelι
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp} (φ : F ⟶ G)
    [HasKernel ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)] :
    (flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep).obj
        (kernel ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)) ⟶ F :=
  (flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep).map
      (kernel.ι ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)) ≫
    (flatBaseChangeQuasicoheratorCompInclusionIsoId B E h S hS p hp hinc hclosed hpres hls hlsD
      hwp hsep).hom.app F

/-- The map of `AlgebraicGeometry.Stack.quasicoheratorKernelι` is annihilated by `φ`, so it is a
kernel fork of `φ`.

The identification `Q ∘ i ≅ 𝟭` is the inverse of the unit of the adjunction, so after
transporting along it the composite becomes `Q` of `Ker(i φ) → i 𝓕 → i 𝓖`, which is `Q` of
zero. -/
theorem quasicoheratorKernelι_comp
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp} (φ : F ⟶ G)
    [HasKernel ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)] :
    quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ ≫ φ = 0 := by
  set Q := flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep
    with hQdef
  set adj := flatBaseChangeQuasicoheratorAdjunction B E h S hS p hp hinc hclosed hpres hls hlsD
    hwp hsep with hadj
  set e := flatBaseChangeQuasicoheratorCompInclusionIsoId B E h S hS p hp hinc hclosed hpres hls
    hlsD hwp hsep with he
  have : Q.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have heinv : e.inv = adj.unit := rfl
  have h1 : e.hom.app F ≫ adj.unit.app F =
      𝟙 (Q.obj ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).obj F)) := by
    have := e.hom_inv_id_app F
    rwa [heinv] at this
  have h2 : adj.unit.app G ≫ e.hom.app G = 𝟙 G := by
    have := e.inv_hom_id_app G
    rwa [heinv] at this
  have hnat : φ ≫ adj.unit.app G =
      adj.unit.app F ≫
        Q.map ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ) :=
    adj.unit.naturality φ
  have hι : quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ =
      Q.map (kernel.ι ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)) ≫
        e.hom.app F := rfl
  have hzero :
      quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ ≫
        φ ≫ adj.unit.app G = 0 := by
    have t1 : 𝟙 (Q.obj ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).obj F)) ≫
        Q.map ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ) =
        Q.map ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ) := Category.id_comp _
    have t2 := Q.map_comp
      (kernel.ι ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ))
      ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)
    have t3 : Q.map (kernel.ι ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ) ≫
        (quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ) = 0 := by
      rw [kernel.condition]
      exact Q.map_zero _ _
    rw [hι, hnat, Category.assoc, ← Category.assoc (e.hom.app F), h1, t1, ← t2, t3]
  calc quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ ≫ φ
      = (quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ ≫
          φ ≫ adj.unit.app G) ≫ e.hom.app G := by
        simp [h2]
    _ = 0 := by rw [hzero, zero_comp]

/-- **Stacks 0GQL, part (3), second half.**  Let `φ : 𝓕 → 𝓖` be a map of quasi-coherent
`𝒪_𝒳`-modules and let `Ker(i φ)` be its kernel inside `LQCoh^fbc(𝒪_𝒳)`.  Then `Q(Ker(i φ))`,
with the map `AlgebraicGeometry.Stack.quasicoheratorKernelι` to `𝓕`, is a kernel of `φ` in
`QCoh(𝒪_𝒳)`.

The proof is formal: `Q` is a right adjoint, so it preserves the kernel, and `Q ∘ i` is the
identity because the inclusion is fully faithful; transporting the kernel of `Q(i φ)` along that
identification gives the kernel of `φ`.

That `Ker(φ)` computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` is the first half of the clause and
is **Stacks 0771** part (2); it is not available, and it enters here only as the instance
hypothesis that the kernel exists in `LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0GQL "part (3), second half: Q(Ker φ) is the kernel of φ in QCoh(𝒪_𝒳), over the \
  existence of Ker φ inside LQCoh^fbc(𝒪_𝒳) — the first half of the clause, which is \
  Stacks 0771 part (2) and is not available"]
def isLimitKernelForkFlatBaseChangeQuasicoherator
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp} (φ : F ⟶ G)
    [HasKernel ((quasicoherentToFlatBaseChange B E h S hS p hp hinc).map φ)] :
    IsLimit (KernelFork.ofι
      (quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ)
      (quasicoheratorKernelι_comp B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ)) := by
  set Q := flatBaseChangeQuasicoherator B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep
    with hQdef
  set i := quasicoherentToFlatBaseChange B E h S hS p hp hinc with hidef
  set adj := flatBaseChangeQuasicoheratorAdjunction B E h S hS p hp hinc hclosed hpres hls hlsD
    hwp hsep with hadj
  set e := flatBaseChangeQuasicoheratorCompInclusionIsoId B E h S hS p hp hinc hclosed hpres hls
    hlsD hwp hsep with he
  letI : Q.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have heinv : e.inv = adj.unit := rfl
  have h1 : ∀ X, e.hom.app X ≫ adj.unit.app X = 𝟙 (Q.obj (i.obj X)) := fun X => by
    have := e.hom_inv_id_app X
    rwa [heinv] at this
  have h2 : ∀ X, adj.unit.app X ≫ e.hom.app X = 𝟙 X := fun X => by
    have := e.inv_hom_id_app X
    rwa [heinv] at this
  have hnat : ∀ {F' G' : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp}
      (ψ : F' ⟶ G'), ψ ≫ adj.unit.app G' = adj.unit.app F' ≫ Q.map (i.map ψ) :=
    fun ψ => adj.unit.naturality ψ
  have hQlim := isLimitOfHasKernelOfPreservesLimit Q (i.map φ)
  have hfork : ∀ {W' : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp}
      (g' : W' ⟶ F), g' ≫ φ = 0 → (g' ≫ adj.unit.app F) ≫ Q.map (i.map φ) = 0 := by
    intro W' g' hg'
    rw [Category.assoc, ← hnat φ, ← Category.assoc, hg', zero_comp]
  have hι : quasicoheratorKernelι B E h S hS p hp hinc hclosed hpres hls hlsD hwp hsep φ =
      Q.map (kernel.ι (i.map φ)) ≫ e.hom.app F := rfl
  refine KernelFork.IsLimit.ofι _ _
    (fun {W'} g' hg' =>
      (KernelFork.IsLimit.lift' hQlim (g' ≫ adj.unit.app F) (hfork g' hg')).1) ?_ ?_
  · intro W' g' hg'
    have hl := (KernelFork.IsLimit.lift' hQlim (g' ≫ adj.unit.app F) (hfork g' hg')).2
    simp only [Fork.ι_ofι] at hl
    rw [hι, ← Category.assoc, hl, Category.assoc]
    simp [h2 F]
  · intro W' g' hg' m hm
    have hkey : m ≫ Q.map (kernel.ι (i.map φ)) = g' ≫ adj.unit.app F := by
      conv_rhs => rw [← hm, hι]
      simp only [Category.assoc, h1 F, Category.comp_id]
    refine hQlim.uniq (KernelFork.ofι (g' ≫ adj.unit.app F) (hfork g' hg')) m ?_
    rintro (_ | _)
    · simpa using hkey
    · have hone : m ≫ Q.map (kernel.ι (i.map φ)) ≫ Q.map (i.map φ) =
          g' ≫ adj.unit.app F ≫ Q.map (i.map φ) := by
        rw [← Category.assoc, hkey, Category.assoc]
      simpa using hone

end AlgebraicGeometry.Stack

end
