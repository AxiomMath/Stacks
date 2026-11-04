module

public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Formal.MinimalVersal.Existence
public import StacksFrontier.Deformation.Formal.VersalObject.ConditionS1
public import StacksFrontier.Deformation.MinimalVersal

/-!
# A minimal versal formal object has no proper descent at any level

Stacks 06T2 produces, for a versal formal object `ξ`, a descent `ξ' → ξ` over a complete
local subalgebra of `ξ.base` with two minimality properties: part (1), that every Artinian
pushforward of `ξ' → ξ` is a minimal object of the descent category, and part (2), that
every morphism of formal objects into `ξ'` is surjective on bases. The library realizes both
as fields of `Deformation.SmallestDescent`, namely `pushforward_minimal` and
`further_descent_surjective`.

Minimal versality (Stacks 06T4, `Deformation.IsMinimalVersal`) is versality plus part (2) for
`ξ` itself. For such a `ξ` the inclusion of its smallest descent is bijective on bases —
injective by `SmallestDescent.base_injective`, surjective by part (2) of the hypothesis
applied to that very inclusion — hence an isomorphism of formal objects, and part (1)
transports to `ξ`. The consequence recorded here is the form in which the proof of Stacks
06T8 uses part (1): the identity descent of each Artinian level `ξ.level n` is minimal, i.e.
an arrow into `ξ.level n` whose base map is injective has surjective base map.

## Main results

* `Deformation.CompleteLocalAlgCat.isIso_of_bijective_hom`: a morphism of
  `\widehat{\mathcal C}_Λ` with bijective underlying algebra map is an isomorphism.
* `Deformation.surjective_of_injective_to_minimalVersal_level`: Stacks **06T2** part (1) for
  a minimal versal formal object, in the form the proof of Stacks 06T8 uses it.

## Implementation notes

The Noetherian and finite-module hypotheses are the chapter conventions of Stacks 06G9, used
here exactly as `Deformation.exists_smallestDescent` and
`Deformation.exists_minimalVersalFormalObject` use them.

`SmallestDescent.pushforward_minimal` is applied at the square whose two pushforward legs are
identities: with `x = ξ.level n`, `y = ξ'.level n` and `g = inclusion.app n`, the two base
maps are the structural `eqToHom`s, which are isomorphisms, so both hom-lift and both
strong-cocartesianness hypotheses are immediate and the range condition is the statement that
composing with an isomorphism does not change an image. What comes out is minimality of the
descent object `g`, and since `g` is an isomorphism every descent object of `ξ.level n` with
an arrow to it — in particular any arrow into `ξ.level n` with injective base map — is an
isomorphism.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
* [Stacks Project, Tag 06T4](https://stacks.math.columbia.edu/tag/06T4)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

section

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of Noetherian complete local `Λ`-algebras with fixed residue field whose
underlying algebra homomorphism is bijective is an isomorphism: the inverse algebra
equivalence is again local and respects the chosen residue-field identifications. -/
public theorem CompleteLocalAlgCat.isIso_of_bijective_hom
    {A B : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (hf : Function.Bijective f.hom) : IsIso f := by
  let e : A ≃ₐ[Λ] B := AlgEquiv.ofBijective f.hom hf
  let s : B ⟶ A :=
    { hom := e.symm.toAlgHom
      isLocal := ⟨fun b hb ↦ by simpa using hb.map e.toRingHom⟩
      residue_comm := fun b ↦
        (f.residue_comm (e.symm b)).symm.trans
          (congrArg (fun z : B => B.residueEquiv (residue B z)) (e.apply_symm_apply b)) }
  exact ⟨s, CompleteLocalAlgCat.Hom.ext (AlgHom.ext e.symm_apply_apply),
    CompleteLocalAlgCat.Hom.ext (AlgHom.ext e.apply_symm_apply)⟩

end

section

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- The underlying algebra map of an isomorphism of Artinian local algebras is bijective. -/
private theorem artinian_bijective_of_isIso {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) [IsIso f] : Function.Bijective f.hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨(inv f).hom, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact congrArg (fun ψ : A ⟶ A ↦ ψ.hom x) (IsIso.hom_inv_id f)
  · exact congrArg (fun ψ : B ⟶ B ↦ ψ.hom x) (IsIso.inv_hom_id f)

/-- **Stacks Project, Tag 06T2**, part (1), for a minimal versal formal object: no Artinian
level of a minimal versal formal object has a proper descent. Any arrow of `F` into
`ξ.level n` whose underlying algebra map is injective has surjective underlying algebra
map. -/
public theorem surjective_of_injective_to_minimalVersal_level
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (hξ : IsMinimalVersal hp.cofibered ξ)
    (n : ℕ) {x : F} (u : x ⟶ ξ.level n)
    (hu : Function.Injective (p.map u).hom) :
    Function.Surjective (p.map u).hom := by
  classical
  obtain ⟨d⟩ := exists_smallestDescent hp.cofibered
    (schlessingerConditionS1_of_versal p hp ξ hξ.1) ξ hξ.1
  have hbase : IsIso d.inclusion.base :=
    CompleteLocalAlgCat.isIso_of_bijective_hom d.inclusion.base
      ⟨d.base_injective, hξ.2 d.object d.inclusion⟩
  let g : d.object.level n ⟶ ξ.level n := d.inclusion.app n
  let : p.IsHomLift ((AdicTruncation.functor n).map d.inclusion.base) g :=
    d.inclusion.app_lift n
  have hgfac : p.map g = eqToHom (d.object.level_eq n) ≫
      (AdicTruncation.functor n).map d.inclusion.base ≫ eqToHom (ξ.level_eq n).symm :=
    IsHomLift.fac' p ((AdicTruncation.functor n).map d.inclusion.base) g
  have hgiso : IsIso (p.map g) := by
    rw [hgfac]
    infer_instance
  have hg : Function.Injective (p.map g).hom := (artinian_bijective_of_isIso (p.map g)).1
  -- the two structural base maps of the pushforward square
  let a : (AdicTruncation.functor n).obj ξ.base ⟶ p.obj (ξ.level n) :=
    eqToHom (ξ.level_eq n).symm
  let b : (AdicTruncation.functor n).obj d.object.base ⟶ p.obj (d.object.level n) :=
    eqToHom (d.object.level_eq n).symm
  let ha : p.IsHomLift a (𝟙 (ξ.level n)) :=
    IsHomLift.of_fac' p a (𝟙 (ξ.level n)) (ξ.level_eq n) rfl (by simp [a])
  let hb : p.IsHomLift b (𝟙 (d.object.level n)) :=
    IsHomLift.of_fac' p b (𝟙 (d.object.level n)) (d.object.level_eq n) rfl (by simp [b])
  have hrange : AlgHom.range (p.map g).hom =
      AlgHom.range (((AdicTruncation.functor n).map d.inclusion.base ≫ a).hom) := by
    have hcomp : (p.map g).hom =
        (((AdicTruncation.functor n).map d.inclusion.base ≫ a).hom).comp
          (eqToHom (d.object.level_eq n) :
            p.obj (d.object.level n) ⟶ (AdicTruncation.functor n).obj d.object.base).hom := by
      rw [hgfac]
      rfl
    have hsurj : Function.Surjective
        (eqToHom (d.object.level_eq n) :
          p.obj (d.object.level n) ⟶ (AdicTruncation.functor n).obj d.object.base).hom :=
      (artinian_bijective_of_isIso (eqToHom (d.object.level_eq n) :
        p.obj (d.object.level n) ⟶ (AdicTruncation.functor n).obj d.object.base)).2
    rw [hcomp, AlgHom.range_comp, (AlgHom.range_eq_top _).mpr hsurj, Algebra.map_top]
  have hmin : IsMinimalObject (⟨Over.mk g, hg⟩ : DescentObject p (ξ.level n)) :=
    d.pushforward_minimal n a b (𝟙 (ξ.level n)) (𝟙 (d.object.level n)) g ha hb
      (Functor.IsStronglyCocartesian.of_isIso (p := p) a (𝟙 (ξ.level n)))
      (Functor.IsStronglyCocartesian.of_isIso (p := p) b (𝟙 (d.object.level n)))
      (by simp [g]) hrange hg
  -- an arrow into `ξ.level n` with injective base map gives a descent object over `g`
  have : IsIso g := isIso_of_isCofiberedInGroupoids_of_map_isIso hp.cofibered g
  let m : (⟨Over.mk u, hu⟩ : DescentObject p (ξ.level n)) ⟶ ⟨Over.mk g, hg⟩ :=
    ObjectProperty.homMk (Over.homMk (u ≫ inv g) (by simp))
  have : IsIso m.hom := (ObjectProperty.isIso_hom_iff m).mpr (hmin _ m)
  have : IsIso (u ≫ inv g) := Functor.map_isIso (Over.forget (ξ.level n)) m.hom
  have : IsIso u := by
    rw [show u = (u ≫ inv g) ≫ g by simp]
    infer_instance
  exact (artinian_bijective_of_isIso (p.map u)).2

end

end Deformation

end
