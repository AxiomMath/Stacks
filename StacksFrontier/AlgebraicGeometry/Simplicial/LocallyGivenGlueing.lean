module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialSystem
import StacksCore.Tactic.StacksAttribute

/-!
# Glueing locally given derived objects over a simplicial object of `SR(B)`

This file proves **Stacks 0DCA**. In Situation 0DC9, assume the negative self-exts of every
`E_U` in `D(O_{u(U)})` vanish. Let `L` be a simplicial object of `SR(B)`, `K = u(L)` and
`((C/K)_total, O)` the ringed site of Remark 0D9W. Then there is a cartesian object `E` of `D(O)`
whose restriction to `D(O_{C/u(U_{n,i})})` is `E_{U_{n,i}}` compatibly, and `E` is unique up to
unique isomorphism.

The proof is the source's. The system `(E_n, E_φ)` assembled from the `E_U`
(`AlgebraicGeometry.RingedSite.LocallyGiven.localSystem`) is cartesian, and its positively
shifted self-maps vanish because they vanish summandwise; so Stacks 0D9T produces `E`. For
uniqueness, Stacks 0D9S and Stacks 0D9R
(`CategoryTheory.CocontinuousSimplicialSite.existsUnique_iso_of_derivedModuleSystem_iso`) apply,
the total site of Remark 0D9W being a case-(B) situation of Situation 09WE.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.exists_unique_cartesian_summandIdentification`:
  **Stacks 0DCA**.

## Implementation notes

"Restricting to `E_{U_{n,i}}` compatibly" is
`AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification`: isomorphisms of the summandwise
restrictions of `E` with the `E_{U_{n,i}}` under which the transitions of `E` are the `ρ_a`. The
proof of the source refers to it as "see proof for details", meaning the identification of the
simplicial system of `E` with the system of the `E_U`; the two are equivalent
(`AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.systemIso`).

"Negative self-exts of `E_U`" are the groups `Ext^{-t}(E_U, E_U) = Hom(E_U[t], E_U)` for `t > 0`.

The simplicial-site infrastructure is monomorphic in the universe `u` of the site, so the
locally given objects are taken with the additional module universe `0`, for which
`AlgebraicGeometry.RingedSite.LocalDerivedCategory` is the derived category of modules in the
universe `u`.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable

universe u uB vB

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))

/-- The positively shifted self-maps of `E_n` vanish when the negative self-exts of the `E_U`
do: they vanish on every summand. -/
theorem systemObj_shift_hom_eq_zero
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} X (G.u.obj U)) t).obj (G.obj U) ⟶ G.obj U,
        g = 0)
    (k : SimplexCategory) (t : ℕ) (ht : 0 < t)
    (g : (shiftFunctor (DerivedCategory ((situation X.J (G.image L)).componentRingedTopos
      (structureSheaf X (G.image L)) k).Modules) (t : ℤ)).obj (G.systemObj L k) ⟶
        G.systemObj L k) : g = 0 :=
  G.shift_hom_eq_zero_of_summandIso L hneg k _ _ (G.systemObjIso L k) (G.systemObjIso L k) t
    (by exact_mod_cast ht) g

variable {G L} in
/-- An isomorphism of objects of `D(O)` is compatible with two summandwise identifications with
the locally given objects exactly when it induces, on simplicial systems, the identification
of the two systems with the system of the locally given objects. -/
theorem SummandIdentification.compatible_iff
    {E E' : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E) (σ' : G.SummandIdentification L E') (ε : E ≅ E') :
    (∀ n : SimplexCategory,
      ((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) n).map ε.hom =
        (σ.systemIso.hom ≫ σ'.systemIso.inv).app n) ↔
    (∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
      (G.summandDerivedRestriction L n i).map (((situation X.J (G.image
          L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) n).map ε.hom) ≫ (σ'.iso n i).hom = (σ.iso n i).hom) :=
  forall_congr' fun n => Functor.eq_comp_inv_iff_pi (G.summandDerivedRestriction L n)
    ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso σ.systemIso)
    ((SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso σ'.systemIso)
    (σ.iso n) (σ'.iso n) (G.systemObjIso L n) (σ.map_systemIso_hom_app n)
    (σ'.map_systemIso_hom_app n) _

/-- **Stacks 0DCA.** In Situation 0DC9, assume the negative self-exts of every `E_U` in
`D(O_{u(U)})` vanish. Let `L` be a simplicial object of `SR(B)`, let `K = u(L)` and let
`((C/K)_total, O)` be the ringed site of Remark 0D9W, with `O = a⁻¹O_C`. Then

* there is a cartesian object `E` of `D(O)` whose restriction to `D(O_{C/u(U_{n,i})})` is
  `E_{U_{n,i}}` compatibly with the isomorphisms `ρ_a` (a
  `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification`), and
* such an `E` is unique up to unique isomorphism: for two of them, `(E, σ)` and `(E', σ')`,
  there is exactly one isomorphism `E ≅ E'` carrying `σ` to `σ'`. -/
@[stacks 0DCA]
theorem exists_unique_cartesian_summandIdentification
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} X (G.u.obj U)) t).obj (G.obj U) ⟶ G.obj U,
        g = 0) :
    (∃ E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
        (structureSheaf X (G.image L))).Modules,
      (situation X.J (G.image L)).IsCartesianDerivedModule (structureSheaf X (G.image L)) E ∧
        Nonempty (G.SummandIdentification L E)) ∧
    ∀ (E E' : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
        (structureSheaf X (G.image L))).Modules),
      (situation X.J (G.image L)).IsCartesianDerivedModule (structureSheaf X (G.image L)) E →
      (situation X.J (G.image L)).IsCartesianDerivedModule (structureSheaf X (G.image L)) E' →
      ∀ (σ : G.SummandIdentification L E) (σ' : G.SummandIdentification L E'),
        ∃! ε : E ≅ E', ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
          (G.summandDerivedRestriction L n i).map
              (((situation X.J (G.image L)).derivedComponentModuleRestriction
                (structureSheaf X (G.image L)) n).map ε.hom) ≫ (σ'.iso n i).hom =
            (σ.iso n i).hom := by
  have hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m),
      ((situation X.J (G.image L)).transitionRingedToposHom (structureSheaf X (G.image L))
        φ).IsFlat := fun _ _ φ => transitionRingedToposHom_isFlat X (G.image L) φ
  refine ⟨?_, fun E E' hE hE' σ σ' => ?_⟩
  · obtain ⟨E, hE, ⟨e⟩⟩ := (situation X.J (G.image
      L)).exists_isCartesianDerivedModule_of_moduleSystem
      (structureSheaf X (G.image L)) hflat (G.localSystem L) (G.localSystem_cartesian L)
      (fun k t ht g => G.systemObj_shift_hom_eq_zero L hneg k t ht g)
    exact ⟨E, hE, ⟨SummandIdentification.ofSystemIso e.symm⟩⟩
  · have hSelf : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
        ∀ g : (shiftFunctor (DerivedCategory ((situation X.J (G.image L)).componentRingedTopos
            (structureSheaf X (G.image L)) k).Modules) (t : ℤ)).obj
            (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L))
              E).obj k) ⟶
            ((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L))
              E).obj k, g = 0 :=
      fun k t ht g => G.shift_hom_eq_zero_of_summandIso L hneg k _ _ (σ.iso k) (σ.iso k) t
        (by exact_mod_cast ht) g
    let e := σ.systemIso ≪≫ σ'.systemIso.symm
    have : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
        (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy
          ((CocontinuousSimplicialSite.situation (simplicialSite X.J (G.image
              L))).transitionRingedToposHom
            (structureSheaf X (G.image L)) φ)).HasLeftDerivedFunctor
          (Stacks.Cohomology.DerivedPushforward.targetQuasiIso
            ((CocontinuousSimplicialSite.situation (simplicialSite X.J (G.image
                L))).componentRingedTopos
              (structureSheaf X (G.image L)) m)) := fun _ _ φ =>
      SimplicialSiteSituation.hasLeftDerivedFunctor_transitionPullbackOnHomotopy _ _ φ
    obtain ⟨ε, hε, huniq⟩ :=
      CategoryTheory.CocontinuousSimplicialSite.existsUnique_iso_of_derivedModuleSystem_iso
        (simplicialSite X.J (G.image L)) (structureSheaf X (G.image L)) hflat E E' hE hE' hSelf e
    refine ⟨ε, (σ.compatible_iff σ' ε).1 hε, fun ε' hε' => huniq ε' ?_⟩
    exact (σ.compatible_iff σ' ε').2 hε'

end AlgebraicGeometry.RingedSite.LocallyGiven
