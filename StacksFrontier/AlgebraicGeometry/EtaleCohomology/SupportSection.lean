module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition

/-!
# The support of a section of an abelian sheaf on the small étale site

Let `F` be an abelian sheaf on the small étale site of a scheme `S` and let `s` be a section
of `F` over an object `U` of that site.  The *zero locus* of `s` is the largest Zariski open
of `U` on which `s` restricts to zero, and the *support* of `s` is its complement.

The zero locus is built as the supremum of those opens of `U` that are the image of an open
immersion `V ⟶ U` in the small étale site along which `s` restricts to zero.  That this
supremum is itself such an open — equivalently, that `s` restricts to zero on every open
immersion whose image lies in the supremum — is the one substantive statement here, and it is
the sheaf axiom: the opens in question cover the supremum, the restrictions of `s` to each of
them vanish, so the restriction of `s` to the supremum is zero by separatedness.  Carrying
that argument out inside a *bounded* big étale site is what the proof spends its length on,
because the covering family indexed by all the opens of the supremum need not be one of the
site's chosen coverings; the site's representability axiom replaces it by a chosen covering
with a combinatorially equivalent family.

## Main definitions

* `AlgebraicGeometry.IsZeroOpen` — the predicate singling out the opens of `U` represented by
  an open immersion in the small étale site along which the section restricts to zero.
* `AlgebraicGeometry.zeroOpen` — the largest Zariski open zero locus of a section.
* `AlgebraicGeometry.supportSection` — its complement, the support of the section.

## Main results

* `AlgebraicGeometry.zero_restrict_iff_image_le_zeroOpen` — a section restricts to zero along
  an open immersion of the small étale site exactly when the image of that immersion is
  contained in the zero locus.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry

/-- A Zariski open on which a section restricts to zero, represented by an
open immersion in the small étale site. -/
public def IsZeroOpen (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) : Prop :=
  ∃ (V : SmallEtale B S hS) (f : V ⟶ U),
    IsOpenImmersion ((SmallEtale.toScheme B S hS).map f) ∧
      (W : Set ((SmallEtale.toScheme B S hS).obj U)) =
        Set.range ((SmallEtale.toScheme B S hS).map f).base ∧
      F.obj.map f.op s = 0

-- `SmallEtale.openEtaleObject`, `SmallEtale.openEtaleInclusion` and
-- `SmallEtale.openEtaleInclusion_map` are not defined here: the uses below are the public ones of
-- `StacksFrontier/AlgebraicGeometry/Etale/FShriekComposition.lean`, which this module imports.

/-- If a section vanishes on an open represented by an open immersion, then it vanishes along
every morphism of the small étale site whose image is contained in that open: the morphism
factors through the immersion. -/
private theorem restrict_eq_zero_of_range_subset_isZeroOpen
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hW : IsZeroOpen B S hS F U s W)
    (V : SmallEtale B S hS) (k : V ⟶ U)
    (hk : Set.range ((SmallEtale.toScheme B S hS).map k).base ⊆ W) :
    F.obj.map k.op s = 0 := by
  classical
  obtain ⟨V₀, f₀, hf₀, hrange, hzero⟩ := hW
  let qScheme := IsOpenImmersion.lift ((SmallEtale.toScheme B S hS).map f₀)
    ((SmallEtale.toScheme B S hS).map k) (by
      rintro x ⟨y, rfl⟩
      rw [← hrange]
      exact hk ⟨y, rfl⟩)
  have hqfac : qScheme ≫ (SmallEtale.toScheme B S hS).map f₀ =
      (SmallEtale.toScheme B S hS).map k :=
    IsOpenImmersion.lift_fac _ _ _
  let qbase := B.inclusion.preimage (show
    B.inclusion.obj V.obj.left ⟶ B.inclusion.obj V₀.obj.left from qScheme)
  have hqmap : B.inclusion.map qbase = qScheme := B.inclusion.map_preimage _
  let f₀base := (Over.forget (B.obj S hS)).map
    ((SmallEtale.inclusion B S hS).map f₀)
  let kbase := (Over.forget (B.obj S hS)).map
    ((SmallEtale.inclusion B S hS).map k)
  have hmapf₀ : B.inclusion.map f₀base = (SmallEtale.toScheme B S hS).map f₀ := rfl
  have hmapk : B.inclusion.map kbase = (SmallEtale.toScheme B S hS).map k := rfl
  have hqbase : qbase ≫ f₀base = kbase := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, hqmap, hmapf₀, hmapk] using hqfac
  have hf₀over : f₀base ≫ U.obj.hom = V₀.obj.hom := by
    simp [f₀base]
  have kover : kbase ≫ U.obj.hom = V.obj.hom := by
    simp [kbase]
  have hqover : qbase ≫ V₀.obj.hom = V.obj.hom := by
    rw [← hf₀over, ← Category.assoc, hqbase, kover]
  let qOver : V.obj ⟶ V₀.obj := Over.homMk qbase hqover
  let q : V ⟶ V₀ := ⟨qOver⟩
  have hq : q ≫ f₀ = k := by
    apply (SmallEtale.toScheme B S hS).map_injective
    change B.inclusion.map (qbase ≫ f₀base) = B.inclusion.map kbase
    rw [hqbase]
  rw [← hq, op_comp, F.obj.map_comp]
  change (F.obj.map q.op) ((F.obj.map f₀.op) s) = 0
  rw [hzero]
  simp

/-- A section vanishing on every member of a chosen covering family vanishes: this is
separatedness of the sheaf for the sieve generated by that family. -/
private alias eq_zero_of_restrict_eq_zero_of_isCovering :=
  AlgebraicGeometry.SmallEtale.section_zero_of_covering

/-- The maximal Zariski open locus on which a section vanishes. -/
public def zeroOpen (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    ((SmallEtale.toScheme B S hS).obj U).Opens :=
  sSup {W | IsZeroOpen B S hS F U s W}

/-- The support of a section is the complement of its maximal Zariski open
zero locus. -/
@[stacks 04FS "support_section"]
public def supportSection (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Set ((SmallEtale.toScheme B S hS).obj U) :=
  (zeroOpen B S hS F U s : Set ((SmallEtale.toScheme B S hS).obj U))ᶜ

/-- On an open immersion, the section vanishes precisely when the image is
contained in the maximal zero open. -/
@[stacks 04FS "support_section"]
public theorem zero_restrict_iff_image_le_zeroOpen (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (V : SmallEtale B S hS) (f : V ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map f)] :
    F.obj.map f.op s = 0 ↔
  ((SmallEtale.toScheme B S hS).map f).opensRange ≤ zeroOpen B S hS F U s :=
  by
    refine ⟨fun hs => le_sSup ⟨V, f, inferInstance, ?_, hs⟩, fun h => ?_⟩
    · ext x
      simp [Scheme.Hom.opensRange]
    classical
    -- the preimages under `f` of the zero opens of `s`, as a family over `V`
    let E : PreZeroHypercover.{u + 1} V := {
      I₀ := ULift.{u + 1, u} {W : ((SmallEtale.toScheme B S hS).obj U).Opens |
        IsZeroOpen B S hS F U s W}
      X i := SmallEtale.openEtaleObject B S hS V
        (((SmallEtale.toScheme B S hS).map f) ⁻¹ᵁ i.down.1)
      f i := SmallEtale.openEtaleInclusion B S hS V
        (((SmallEtale.toScheme B S hS).map f) ⁻¹ᵁ i.down.1)
    }
    let G := SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)
    have hmapEi (i : E.I₀) : ((E.map G).map B.inclusion).f i =
        ((SmallEtale.toScheme B S hS).map f ⁻¹ᵁ i.down.1).ι :=
      SmallEtale.openEtaleInclusion_map B S hS V _
    -- since `f` lands in the zero locus, they form an étale covering
    have hEtale : IsEtaleCovering ⟨V.obj.left, E.map G⟩ := by
      refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) _).2 ⟨fun x => ?_, fun i => ?_⟩
      · obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp (h ⟨x, rfl⟩)
        refine ⟨ULift.up ⟨W, hW⟩, ⟨x, hxW⟩, ?_⟩
        rw [hmapEi]
        rfl
      · have : IsOpenImmersion (((E.map G).map B.inclusion).f i) := by
          rw [hmapEi i, Scheme.Opens.ι]
          exact IsOpenImmersion.ofRestrict _ _
        infer_instance
    -- a morphism factoring through a member of `E` maps, after `f`, into its zero open
    have hrange (j : E.I₀) {Y : SmallEtale B S hS} (g : Y ⟶ V)
        (e : (SmallEtale.toScheme B S hS).obj Y ⟶ (SmallEtale.toScheme B S hS).obj (E.X j))
        (hg : (SmallEtale.toScheme B S hS).map g =
          e ≫ (SmallEtale.toScheme B S hS).map (E.f j)) :
        Set.range ((SmallEtale.toScheme B S hS).map (g ≫ f)).base ⊆ j.down.1 := by
      rintro x ⟨y, rfl⟩
      rw [Functor.map_comp, hg,
        show (SmallEtale.toScheme B S hS).map (E.f j) = _ from hmapEi j]
      exact (e.base y).property
    -- refine the covering to a covering of the small étale site and glue the zero restrictions
    obtain ⟨⟨Rtarget, Rfam⟩, hR, hcomb⟩ := B.exists_covering_rep _ hEtale
    obtain rfl : V.obj.left = Rtarget := hcomb.1
    obtain ⟨α, hX, hf⟩ := hcomb.2.symm.1
    have hRprops :
        (∀ x, ∃ i, x ∈ Set.range ((Rfam.map B.inclusion).f i)) ∧
          ∀ i, Etale ((Rfam.map B.inclusion).f i) := by
      simpa only [Scheme.etalePrecoverage] using
        (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (Rfam.map B.inclusion)).1 hR.1
    let Rsmall : PreZeroHypercover.{u + 1} V := {
      I₀ := Rfam.I₀
      X i := ⟨Over.mk (Rfam.f i ≫ V.obj.hom), by
        change Etale (B.inclusion.map (Rfam.f i) ≫ B.inclusion.map V.obj.hom)
        have : Etale (B.inclusion.map (Rfam.f i)) := hRprops.2 i
        exact Etale.etale_comp _ _⟩
      f i := ⟨Over.homMk (Rfam.f i) rfl⟩
    }
    have hRsmall : SmallEtale.IsCovering B S hS ⟨V, Rsmall⟩ := by
      change B.IsCovering ⟨V.obj.left, Rsmall.map G⟩
      rwa [show Rsmall.map G = Rfam by ext <;> rfl]
    refine eq_zero_of_restrict_eq_zero_of_isCovering B S hS F V Rsmall hRsmall _ fun i => ?_
    have hg : (SmallEtale.toScheme B S hS).map (Rsmall.f i) =
        B.inclusion.map (eqToHom (hX i)) ≫ (SmallEtale.toScheme B S hS).map (E.f (α i)) := by
      change B.inclusion.map (Rfam.f i) = _
      rw [hf i, Functor.map_comp]
      rfl
    simpa only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply] using
      restrict_eq_zero_of_range_subset_isZeroOpen B S hS F U s _ (α i).down.2 (Rsmall.X i)
        (Rsmall.f i ≫ f) (hrange (α i) (Rsmall.f i) _ hg)

end AlgebraicGeometry
