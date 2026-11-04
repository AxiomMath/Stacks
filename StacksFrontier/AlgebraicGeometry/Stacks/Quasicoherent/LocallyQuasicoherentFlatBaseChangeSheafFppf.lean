module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeSheaf

/-!
# `LQCoh^fbc(𝒪_𝒳)` inside `Mod(𝒪_𝒳)` (Stacks 0771)

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_{fppf}`.  `LQCoh^fbc(𝒪_𝒳)` is the full
subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` of the locally quasi-coherent modules (**Stacks 06WJ**) with
the flat base change property of **Stacks 0762**, read on sheaves of modules as in the source:
the weak Serre class `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheaf`.

**Stacks 0771** (1) says that such a module is a sheaf for the fppf topology, i.e. an object of
`Mod(𝒪_𝒳)`, the modules on the associated fppf site.  This file turns that into a functor

`j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`,

which is the identity on the underlying presheaves of modules, and proves that it is fully
faithful and exact.

## Main definitions

* `AlgebraicGeometry.Stack.fppfToEtaleSheafOfModules`: restriction `Mod(𝒪_𝒳) ⥤ Mod(𝒳_étale, 𝒪_𝒳)`
  from the fppf to the étale topology, fully faithful.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafToFppf`: **Stacks 0771 (1)** as
  the functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithfulLocallyQuasicoherentFlatBaseChangeSheafToFppf`: `j` is
  fully faithful.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafToFppfCompIso`: `j` followed
  by restriction to the étale topology is the inclusion of `LQCoh^fbc(𝒪_𝒳)` into
  `Mod(𝒳_étale, 𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_locallyQuasicoherentFlatBaseChangeSheafToFppf`
  and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_locallyQuasicoherentFlatBaseChangeSheafToFppf`:
  `j` is exact, kernels and cokernels in `LQCoh^fbc(𝒪_𝒳)` being those of `Mod(𝒳_étale, 𝒪_𝒳)`,
  which are already fppf sheaves.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Restriction of modules from the fppf to the étale topology.**  The underlying presheaf of
modules and the presheaf of rings it is a module over are unchanged; only the sheaf condition is
weakened to the one for the coarser étale topology. -/
def fppfToEtaleSheafOfModules :
    SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) where
  obj M := ⟨M.val, M.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)⟩
  map f := ⟨f.val⟩

/-- Restriction from the fppf to the étale topology is fully faithful: a morphism of sheaves of
modules is a morphism of the underlying presheaves of modules. -/
def fullyFaithfulFppfToEtaleSheafOfModules :
    (fppfToEtaleSheafOfModules B S hS p hp).FullyFaithful where
  preimage f := ⟨f.val⟩

/-- Restriction from the fppf to the étale topology is full. -/
instance : (fppfToEtaleSheafOfModules B S hS p hp).Full :=
  (fullyFaithfulFppfToEtaleSheafOfModules B S hS p hp).full

/-- Restriction from the fppf to the étale topology is faithful. -/
instance : (fppfToEtaleSheafOfModules B S hS p hp).Faithful :=
  (fullyFaithfulFppfToEtaleSheafOfModules B S hS p hp).faithful

/-- The functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`.  A sheaf of
`𝒪_𝒳`-modules on `𝒳_étale` which is locally quasi-coherent and has the flat base change property
is a sheaf for the fppf topology, by
`AlgebraicGeometry.Stack.isSheaf_fppf_of_locallyQuasicoherentFlatBaseChangeSheaf` (Stacks 076T),
hence a module on the associated fppf site.  Only the sheaf condition is improved, so `j` is the
identity on the underlying presheaves of modules and on morphisms. -/
def locallyQuasicoherentFlatBaseChangeSheafToFppf :
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).FullSubcategory ⥤
      SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) where
  obj F := ⟨F.obj.val,
    isSheaf_fppf_of_locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp F.property⟩
  map f := ⟨f.hom.val⟩

/-- `j` followed by restriction to the étale topology is the inclusion of `LQCoh^fbc(𝒪_𝒳)` into
`Mod(𝒳_étale, 𝒪_𝒳)`; both are the identity on underlying presheaves of modules. -/
def locallyQuasicoherentFlatBaseChangeSheafToFppfCompIso :
    locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp ⋙
        fppfToEtaleSheafOfModules B S hS p hp ≅
      (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).ι :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- **`j` is fully faithful**: neither the sheaf condition nor the morphisms change. -/
def fullyFaithfulLocallyQuasicoherentFlatBaseChangeSheafToFppf :
    (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).FullyFaithful where
  preimage f := ObjectProperty.homMk ⟨f.val⟩

/-- The functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` is full. -/
instance : (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).Full :=
  (fullyFaithfulLocallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).full

/-- The functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` is faithful. -/
instance : (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).Faithful :=
  (fullyFaithfulLocallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).faithful

section Exactness

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`j` is left exact.**  Restriction to the étale topology is fully faithful, so it reflects
limits, and `j` followed by it is the inclusion of the weak Serre class `LQCoh^fbc(𝒪_𝒳)`, which
preserves finite limits. -/
theorem preservesFiniteLimits_locallyQuasicoherentFlatBaseChangeSheafToFppf :
    PreservesFiniteLimits (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp) := by
  have : PreservesFiniteLimits (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp ⋙
      fppfToEtaleSheafOfModules B S hS p hp) :=
    have := (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p
      hp).preservesFiniteLimits_ι_of_isWeakSerreClass
    preservesFiniteLimits_of_natIso
      (locallyQuasicoherentFlatBaseChangeSheafToFppfCompIso B E h S hS p hp).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp)
    (fppfToEtaleSheafOfModules B S hS p hp)

/-- **`j` is right exact.**  As for
`AlgebraicGeometry.Stack.preservesFiniteLimits_locallyQuasicoherentFlatBaseChangeSheafToFppf`:
the inclusion of the weak Serre class `LQCoh^fbc(𝒪_𝒳)` into `Mod(𝒳_étale, 𝒪_𝒳)` preserves finite
colimits, its cokernels being cokernels of étale modules, and restriction to the étale topology
reflects them. -/
theorem preservesFiniteColimits_locallyQuasicoherentFlatBaseChangeSheafToFppf :
    PreservesFiniteColimits (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp) := by
  have : PreservesFiniteColimits (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp ⋙
      fppfToEtaleSheafOfModules B S hS p hp) :=
    have := (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p
      hp).preservesFiniteColimits_ι_of_isWeakSerreClass
    preservesFiniteColimits_of_natIso
      (locallyQuasicoherentFlatBaseChangeSheafToFppfCompIso B E h S hS p hp).symm
  exact preservesFiniteColimits_of_reflects_of_preserves
    (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp)
    (fppfToEtaleSheafOfModules B S hS p hp)

end Exactness

/-! ### `LQCoh^fbc(𝒪_𝒳)` as a subcategory of `Mod(𝒪_𝒳)` -/

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`**: a module on the associated fppf site belongs to it when its
restriction to the étale topology is locally quasi-coherent (**Stacks 06WJ**) and has the flat
base change property of **Stacks 0762** read on sheaves of modules. -/
abbrev locallyQuasicoherentFlatBaseChangeSheafFppf :
    ObjectProperty (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :=
  (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).inverseImage
    (fppfToEtaleSheafOfModules B S hS p hp)

/-- Every module `j(F)` lies in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. -/
theorem locallyQuasicoherentFlatBaseChangeSheafFppf_obj
    (F : (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).FullSubcategory) :
    locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp
      ((locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).obj F) :=
  F.property

/-- Restriction from the fppf to the étale topology is additive. -/
instance : (fppfToEtaleSheafOfModules B S hS p hp).Additive where
  map_add := rfl

/-- The functor `j : LQCoh^fbc(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` is additive. -/
instance : (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).Additive where
  map_add := rfl

section WeakSerre

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction from the fppf to the étale topology is left exact: both categories compute finite
limits on underlying presheaves of modules, and restriction is the identity there. -/
instance preservesFiniteLimits_fppfToEtaleSheafOfModules :
    PreservesFiniteLimits (fppfToEtaleSheafOfModules B S hS p hp) := by
  have : PreservesFiniteLimits (fppfToEtaleSheafOfModules B S hS p hp ⋙
      SheafOfModules.forget (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))) :=
    @preservesFiniteLimits_of_natIso _ _ _ _
      (SheafOfModules.forget.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) _
      (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)
      (SheafOfModules.Finite.forgetPreservesFiniteLimits.{u}
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
  exact ⟨fun J _ _ => ⟨fun {K} => preservesLimit_of_reflects_of_preserves
    (fppfToEtaleSheafOfModules B S hS p hp) (SheafOfModules.forget _)⟩⟩

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` contains a zero object. -/
instance containsZero_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).ContainsZero :=
  inferInstance

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsClosedUnderIsomorphisms :=
  inferInstance

/-- **The kernel clause of Stacks 0771 (2) for `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`.**  The kernel of a
map of `Mod(𝒪_𝒳)` is the same whether computed in the fppf or the étale topology, so this is the
kernel clause of the étale weak Serre class. -/
instance isClosedUnderKernels_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) ?_
    exact (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).prop_of_iso
      (PreservesKernel.iso (fppfToEtaleSheafOfModules B S hS p hp) f).symm
      ((locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).prop_kernel _ hM hN)

/-- **The cokernel clause of Stacks 0771 (2) for `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`.**  The cokernel in
the étale topology of a map of members is a member, hence an fppf sheaf by Stacks 0771 (1); so it
is already the cokernel in `Mod(𝒪_𝒳)`, restriction to the étale topology being fully faithful. -/
instance isClosedUnderCokernels_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    set R := fppfToEtaleSheafOfModules B S hS p hp
    set P := locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp
    have hC : P (cokernel (R.map f)) := P.prop_cokernel _ hM hN
    let C : P.FullSubcategory := ⟨cokernel (R.map f), hC⟩
    let jC := (locallyQuasicoherentFlatBaseChangeSheafToFppf B E h S hS p hp).obj C
    let π : _ ⟶ jC := (fullyFaithfulFppfToEtaleSheafOfModules B S hS p hp).preimage
      (cokernel.π (R.map f))
    have hπ : R.map π = cokernel.π (R.map f) :=
      (fullyFaithfulFppfToEtaleSheafOfModules B S hS p hp).map_preimage _
    have w : f ≫ π = 0 := R.map_injective (by
      rw [Functor.map_comp, Functor.map_zero]
      exact (congrArg (R.map f ≫ ·) hπ).trans (cokernel.condition (R.map f)))
    have hcol : IsColimit (CokernelCofork.ofπ π w) := by
      apply isColimitOfReflects R
      refine (isColimitMapCoconeCoforkEquiv' R w).symm ?_
      refine IsColimit.ofIsoColimit (cokernelIsCokernel (R.map f)) ?_
      exact Cofork.ext (Iso.refl _) (by simp only [Cofork.π_ofπ, hπ]; exact Category.comp_id _)
    exact (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso hcol hk) hC

end WeakSerre

/-! ### At the seating of an essentially small `𝒳` -/

section EssentiallySmall

variable {𝒴 : Type (u + 1)} [Category.{u} 𝒴] [EssentiallySmall.{u} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)

/-- The weak Serre property of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)`, with the flat
base change property read on sheaves of modules as in the source: `LQCoh^fbc(𝒪_𝒳)` is a weak
Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`.  The sheafification conditions under which
`Mod(𝒳_étale, 𝒪_𝒳)` is abelian hold because `𝒳` is essentially small. -/
theorem isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheaf_etale :
    letI : HasSheafify (associatedTopology B S hS q (etaleTopology B)) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    letI : (associatedTopology B S hS q (etaleTopology B)).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS q hq).IsWeakSerreClass :=
  inferInstance

end EssentiallySmall

end AlgebraicGeometry.Stack

end
