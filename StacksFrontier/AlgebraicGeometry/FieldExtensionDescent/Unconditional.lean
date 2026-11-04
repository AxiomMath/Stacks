module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.FieldExtension
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.AmpleOpening
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Ampleness and quasi-projectivity descend along any field extension

A scheme `X` over a field `k` carries an ample invertible sheaf as soon as its base change `X_K`
to some field extension `K/k` does, and `X` is quasi-projective over `k` as soon as `X_K` is
quasi-projective over `K`.

## Main results

* `AlgebraicGeometry.FieldExtensionDescent.exists_isAmple_baseChangeDiagram_obj`: an ample
  invertible sheaf on `X_K` descends to an ample invertible sheaf on the base change of `X` to
  some finitely generated `k`-subalgebra of `K`.
* `AlgebraicGeometry.exists_isAmple_of_fieldExtension`: if `X_K` has an ample invertible sheaf,
  so does `X`.
* `AlgebraicGeometry.isQuasiProjective_of_fieldExtension`: if `X_K` is quasi-projective over
  `K`, then `X` is quasi-projective over `k`.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace AlgebraicGeometry.FieldExtensionDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (.of k))

/-- **Ample invertible sheaves descend to a finitely generated subalgebra.** An ample invertible
sheaf on `X_K` descends to an ample invertible sheaf on the base change of `X` to some finitely
generated `k`-subalgebra of `K`. -/
public theorem exists_isAmple_baseChangeDiagram_obj
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).Modules)
    [inst : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace.presheaf
      (structureSheafRing
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace).property L]
    (hamp : Scheme.Modules.IsAmple
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) :
    ∃ (i : (FGSubalgebra k K)ᵒᵖ) (N : ((baseChangeDiagram k K f).obj i).Modules),
      ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        ((baseChangeDiagram k K f).obj i).toRingedSpace.presheaf
        (structureSheafRing ((baseChangeDiagram k K f).obj i).toRingedSpace).property N,
        Scheme.Modules.IsAmple ((baseChangeDiagram k K f).obj i) N := by
  obtain ⟨i, Lᵢ, hLᵢ, ⟨e⟩⟩ := exists_isInvertible_baseChangeDiagram_pullback_iso k K f L inst
  have hi : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((baseChangeDiagram k K f).obj i).toRingedSpace.presheaf
      (structureSheafRing ((baseChangeDiagram k K f).obj i).toRingedSpace).property Lᵢ := hLᵢ
  have hpb : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace.presheaf
      (structureSheafRing
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace).property
      ((Scheme.Modules.pullback ((baseChangeLimitCone k K f).cone.π.app i)).obj Lᵢ) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      ((baseChangeLimitCone k K f).cone.π.app i).toLRSHom.toShHom Lᵢ
  have hamp' : Scheme.Modules.IsAmple
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
      ((Scheme.Modules.pullback ((baseChangeLimitCone k K f).cone.π.app i)).obj Lᵢ) :=
    Scheme.Modules.isAmple_of_iso e hamp
  obtain ⟨j, g, hj⟩ := exists_isAmple_pullback_baseChangeDiagram_map k K f i Lᵢ hamp'
  exact ⟨j, _, inferInstance, hj⟩

end AlgebraicGeometry.FieldExtensionDescent

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- Let `k` be a field and `X` a scheme over `k`. If there exists an ample invertible sheaf on
`X_K` for some field extension `K/k`, then `X` has an ample invertible sheaf. -/
@[stacks 0BDC]
public theorem exists_isAmple_of_fieldExtension
    (h : ∃ L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).Modules,
        ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace.presheaf
          (structureSheafRing
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace).property L,
          Scheme.Modules.IsAmple
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) :
    ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
      Scheme.Modules.IsAmple X M := by
  obtain ⟨L, hL, hamp⟩ := h
  have hcs : CompactSpace X := compactSpace_of_isAmple_baseChange k K f L hamp
  have hqs : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_isAmple_baseChange k K f L hamp
  obtain ⟨i, N, hN, hampN⟩ :=
    FieldExtensionDescent.exists_isAmple_baseChangeDiagram_obj k K f L hamp
  exact exists_isAmple_of_finiteType_base_change k
    (i.unop : Subalgebra k K) f ⟨N, hN, hampN⟩

/-- Let `k` be a field and `X` a scheme over `k`. If `X_K` is quasi-projective over `K` for some
field extension `K/k`, then `X` is quasi-projective over `k`. -/
@[stacks 0BDE, ega "IV 9.1.5" "quasi-projective case", ega "II 6.6.5" "quasi-proj. descent"]
public theorem isQuasiProjective_of_fieldExtension
    (h : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsQuasiProjective f :=
  isQuasiProjective_of_fieldExtension_of_exists_isAmple_comm k K f
    (exists_isAmple_of_fieldExtension k K f) h

end AlgebraicGeometry

end
