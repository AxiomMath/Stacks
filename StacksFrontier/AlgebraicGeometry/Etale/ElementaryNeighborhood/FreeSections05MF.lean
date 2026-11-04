module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsLocalBase
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.EtaleNeighborhoodFreeSections

/-!
# Free sections near a flat point after an elementary étale base change

Stacks Tag 05MF says: for `f : X ⟶ S` locally of finite type and `F` a finite type quasi-coherent
`𝒪_X`-module which is flat over `S` at `x`, there is an affine elementary étale neighbourhood
`(S', s')` of `(S, f x)` and an affine open `U'` of `X ×_S Spec 𝒪_{S', s'}` containing the point
`x' = (x, s')` on which `Γ(U', F|_{U'})` is a free `𝒪_{S', s'}`-module.

Its conclusion is a conjunction of five clauses about the produced data: that `x'` lies over `x`,
that `x'` lies over the distinguished point of the neighbourhood, that `U'` is affine, that `x'`
lies in `U'`, and that the sections are free. This file discharges the second clause outright and
reduces the fifth to projectivity, leaving the obligation stated in
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections` as its hypothesis `hproj`,
which is exactly what the source defers to Lemma 05ME (combined with Proposition 05I5).

For `f` locally of finite presentation and `F` of finite presentation that obligation is
discharged here: it is Lemma 05ME base changed along `Spec 𝒪_{S', s'} ⟶ S'`, which is
`AlgebraicGeometry.exists_affineOpen_projective_sections_stalk`. What the general statement still
waits on is the source's two reductions to that case — the closed immersion of an affine
neighbourhood of `x` into an affine space over `S`, which makes the morphism of finite
presentation, and Proposition 05I5, which makes the module of finite presentation after a further
elementary étale base change.

The second clause is automatic because of the shape of the base change: the base of
`X ×_S Spec 𝒪_{S', s'}` is `Spec` of the local ring of `S'` at `s'`, and for an *étale* structure
morphism the only point of `Spec 𝒪_{S', s'}` whose image in `S` is `f x` is the one lying over
`s'` (`AlgebraicGeometry.Scheme.eq_of_fromSpecStalk_eq`). So any point of the fibre product over
`x` lies over `s'` with no further hypothesis, elementariness included. The fifth clause is
Kaplansky's theorem, already isolated as
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_projective_sections`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.fromSpecStalk_snd_eq_point`: a point of
  `X ×_S Spec 𝒪_{U, u}` lying over `x` automatically lies over the distinguished point `u`.
* `AlgebraicGeometry.EtaleNeighborhood.exists_point_fst_eq`: such a point exists.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections`: the statement of Tag 05MF,
  from the obligation in which the sections are only *projective* and nothing is said about the
  image of the point in `Spec 𝒪_{S', s'}`.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_unique_point`: the same
  conclusion with `x'` identified as *the unique* point over `x`, which is what the source says.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finitePresentation`:
  Tag 05MF outright, with no obligation, for `f` locally of finite presentation and `F` of finite
  presentation. There the obligation is Lemma 05ME base changed to the local scheme of the
  neighbourhood it produces,
  `AlgebraicGeometry.exists_affineOpen_projective_sections_stalk`.

## Implementation notes

The hypothesis `hproj` is an implication from the flatness hypothesis rather than a bare
existential, so that the flatness of `F` over `S` at `x` is consumed where the source consumes
it — inside Proposition 05I5 and Lemma 05ME — and not restated.

The clause `IsAffine N.scheme` is left in the obligation. Shrinking a non-affine elementary étale
neighbourhood to an affine open around its distinguished point changes the local ring by a
canonical isomorphism rather than leaving it equal, so the affine case cannot be reached from the
general one without transporting the whole conclusion along that isomorphism.

## References

* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 05ME](https://stacks.math.columbia.edu/tag/05ME)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace EtaleNeighborhood

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (N : EtaleNeighborhood S (f x))

/-- A point of `X ×_S Spec 𝒪_{U, u}` which lies over `x` lies over the distinguished point `u` of
the étale neighbourhood `U`: its image in `Spec 𝒪_{U, u}` has image `f x` in `S`, and for an étale
structure morphism the only such point of `Spec 𝒪_{U, u}` is the one lying over `u`.

No elementariness is needed; this is the clause `x' = (x, s')` of Tags 05I5, 05ID, 05KY, 05KZ and
05MF which concerns the second coordinate. -/
theorem fromSpecStalk_snd_eq_point
    {x' : ↥(pullback f (N.scheme.fromSpecStalk N.point ≫ N.toBase))}
    (hx' : pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x' = x) :
    N.scheme.fromSpecStalk N.point
      (pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x') = N.point := by
  obtain ⟨y, hy⟩ := exists_fromSpecStalk_eq_point f x N
  have hcond : f (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x') =
      (N.scheme.fromSpecStalk N.point ≫ N.toBase)
        (pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x') :=
    congr($(pullback.condition (f := f)
      (g := N.scheme.fromSpecStalk N.point ≫ N.toBase)) x')
  rw [hx', Scheme.Hom.comp_apply] at hcond
  have h : N.toBase (N.scheme.fromSpecStalk N.point
      (pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x')) = N.toBase N.point := by
    rw [N.map_point]
    exact hcond.symm
  rw [Scheme.eq_of_fromSpecStalk_eq N.toBase N.point hy h, hy]

/-- `X ×_S Spec 𝒪_{U, u}` has a point lying over `x`, and it lies over the distinguished point `u`
of the étale neighbourhood `U`. This is the clause `x' = (x, s')` of Tags 05I5, 05ID, 05KY, 05KZ
and 05MF, in existence form and with no elementariness hypothesis; for an elementary
neighbourhood `AlgebraicGeometry.EtaleNeighborhood.exists_preimage_fst_eq_singleton` says in
addition that there is no other point over `x`. -/
theorem exists_point_fst_eq :
    ∃ x' : ↥(pullback f (N.scheme.fromSpecStalk N.point ≫ N.toBase)),
      pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x' = x ∧
        N.scheme.fromSpecStalk N.point
          (pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase) x') = N.point := by
  obtain ⟨y, hy⟩ := exists_fromSpecStalk_eq_point f x N
  have hcond : f x = (N.scheme.fromSpecStalk N.point ≫ N.toBase) y := by
    rw [Scheme.Hom.comp_apply, hy, N.map_point]
  obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hcond
  exact ⟨x', hx', fromSpecStalk_snd_eq_point f x N hx'⟩

end EtaleNeighborhood

/-- **Stacks Project, Tag 05MF.** A finite-type quasi-coherent module which is flat over the base
at a point has free sections on an affine neighbourhood of the lifted point after base change to
the local scheme of an affine elementary étale neighbourhood.

The obligation `hproj` is Lemma 05ME composed with Proposition 05I5: the same existential with
`Module.Projective` in place of `Module.Free`, and with nothing asserted about the image of `x'`
in `Spec 𝒪_{S', s'}`. Projectivity becomes freeness by Kaplansky's theorem (Tag 0593), and the
image of `x'` is the distinguished point automatically, by
`AlgebraicGeometry.EtaleNeighborhood.fromSpecStalk_snd_eq_point`. -/
@[stacks 05MF "RESTRICTED: carries hproj, this same existential with Module.Projective in place of
Module.Free and the clause on the image of x' in Spec 𝒪_{S', s'} dropped, which is the 05ME half
of the source's proof (Lemma 05ME composed with Proposition 05I5)"]
theorem exists_elementaryEtaleNeighborhood_free_sections
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hproj : IsFlatOverAt f.toLRSHom.toShHom F x →
      ∃ (N : EtaleNeighborhood S (f x)),
        N.IsElementary ∧ IsAffine N.scheme ∧
          let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
          let P := pullback f g
          ∃ (x' : P) (W : P.Opens),
            pullback.fst f g x' = x ∧
              IsAffineOpen W ∧ x' ∈ W ∧
                let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
                letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                  Module.compHom Γ(F', W)
                    (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                      (pullback.snd f g).appLE ⊤ W (by simp)).hom)
                Module.Projective (N.scheme.presheaf.stalk N.point) Γ(F', W)) :
    ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Free (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  obtain ⟨N, helem, haffine, x', W, hfst, hW, hxW, hP⟩ := hproj hflat
  refine exists_elementaryEtaleNeighborhood_free_sections_of_projective_sections f F x
    ⟨N, helem, haffine, x', W, hfst,
      EtaleNeighborhood.fromSpecStalk_snd_eq_point f x N hfst, hW, hxW, hP⟩

/-- **Stacks Project, Tag 05MF**, with the point `x'` identified as *the unique* point of
`X ×_S Spec 𝒪_{S', s'}` lying over `x`, which is the form in which the source states it. The
uniqueness is `AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`, and it
is where elementariness of the neighbourhood is used. -/
theorem exists_elementaryEtaleNeighborhood_free_sections_unique_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hproj : IsFlatOverAt f.toLRSHom.toShHom F x →
      ∃ (N : EtaleNeighborhood S (f x)),
        N.IsElementary ∧ IsAffine N.scheme ∧
          let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
          let P := pullback f g
          ∃ (x' : P) (W : P.Opens),
            pullback.fst f g x' = x ∧
              IsAffineOpen W ∧ x' ∈ W ∧
                let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
                letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                  Module.compHom Γ(F', W)
                    (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                      (pullback.snd f g).appLE ⊤ W (by simp)).hom)
                Module.Projective (N.scheme.presheaf.stalk N.point) Γ(F', W)) :
    ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g ⁻¹' {x} = {x'} ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Free (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  obtain ⟨N, helem, haffine, x', W, hfst, hsnd, hW, hxW, hfree⟩ :=
    exists_elementaryEtaleNeighborhood_free_sections f F x hflat hproj
  exact ⟨N, helem, haffine, x', W,
    EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq f x N helem hfst,
    hsnd, hW, hxW, hfree⟩

/-- **Stacks Project, Tag 05MF** for a morphism locally of finite presentation and a module of
finite presentation, with no hypothesis beyond flatness at the point.

Under those hypotheses the obligation `hproj` of
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections` is Lemma 05ME base changed to
the local scheme of the neighbourhood it produces, which is
`AlgebraicGeometry.exists_affineOpen_projective_sections_stalk`. The source states Tag 05MF for
`f` locally of finite *type* and `F` of finite type, and reaches the hypotheses used here by a
closed immersion into affine space and by Proposition 05I5; those two reductions are what the
general statement still waits on. -/
@[stacks 05MF "for f locally of finite presentation and F of finite presentation"]
theorem exists_elementaryEtaleNeighborhood_free_sections_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            N.scheme.fromSpecStalk N.point (pullback.snd f g x') = N.point ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Free (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  let : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  exact exists_elementaryEtaleNeighborhood_free_sections f F x hflat fun _ =>
    exists_affineOpen_projective_sections_stalk f F x hflat

end AlgebraicGeometry

end
