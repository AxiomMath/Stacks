module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus0BDP
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# A fibrewise free module over a reduced base is pulled back from the base

Let `f : X ⟶ S` be a morphism of schemes and `E` a finite locally free module on `X` whose
restriction to every scheme-theoretic fibre `X_s` is free of finite rank. Then the descent locus
of `E` of [Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) contains every point of
`S`, so its immersion is a surjective closed immersion; when `S` is reduced such an immersion is
an isomorphism, and therefore `E` is the pullback of a finite locally free module on `S`. This is
[Stacks, Tag 0EX7](https://stacks.math.columbia.edu/tag/0EX7).

## Main results

* `AlgebraicGeometry.descendsFromBase_of_nonempty_iso_free`: a base change along which `E`
  becomes free of finite rank satisfies the descent condition of Tag 0BDP.
* `AlgebraicGeometry.IsDescentLocus.isIso_hom_of_forall_descendsFromBase`: over a reduced base, a
  descent locus through which every residue field factors is the whole base.
* `AlgebraicGeometry.IsDescentLocus.exists_finiteLocallyFree_iso_of_fiberwiseFree`: the
  conclusion of Tag 0EX7 for a given descent locus.
* `AlgebraicGeometry.exists_finiteLocallyFree_iso_of_fiberwiseFree`: the same conclusion from
  representability of the descent condition.

## Implementation notes

The fibre `X_s` is the base change of `f` along `S.fromSpecResidueField s`, and the restriction of
`E` to it is the pullback along `pullback.fst`, which is the spelling of a fibre used throughout
the descent-locus files. Freeness of rank `r` on the fibre is an isomorphism with
`SheafOfModules.free (ULift (Fin r))`, and the module on the base witnessing the descent condition
there is the free module of the same rank, by
`RingedSpaceModuleAdjunction.modulePullbackObjFreeIso`.

Representability of the descent condition — the existence statement of Tag 0BDP, which is
`AlgebraicGeometry.HasDescentLocus` — is not available in this library, so it appears as an
explicit hypothesis rather than being discharged. It is a *necessary* hypothesis: as
`AlgebraicGeometry.hasDescentLocus_of_exists_finiteLocallyFree_iso` shows, the conclusion of
Tag 0EX7 implies it. The `@[stacks 0EX7]` attribute on
`AlgebraicGeometry.exists_finiteLocallyFree_iso_of_fiberwiseFree` therefore carries the scope
label `"assuming the representability of the descent locus of Tag 0BDP"`: the tag asserts its
conclusion outright, whereas what is proved here is its reduction to representability, and the
label records that gap wherever the attribute is read.

## References

* [Stacks Project, Tag 0EX7](https://stacks.math.columbia.edu/tag/0EX7)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

namespace SheafOfModules

/-- The free module on `r` generators over a scheme is finite locally free: it is finite locally
free of rank `r`, and a module of fixed finite rank is finite locally free. -/
theorem isFiniteLocallyFree_free (T : Scheme.{u}) (r : ℕ) :
    IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := structureSheafRing T.toRingedSpace) (ULift.{u} (Fin r))) :=
  IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (_root_.SheafOfModules.free (R := structureSheafRing T.toRingedSpace) (ULift.{u} (Fin r))) r
    (hM := isFiniteLocallyFreeOfRank_free.{u, u, u} r)

end SheafOfModules

/-- Pulling back along a composite of scheme morphisms is pulling back along each in turn. -/
private noncomputable def modulePullbackIsoOfComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hfg : f ≫ g = h)
    (N : _root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    (modulePullback h.toLRSHom.toShHom).obj N ≅
      (modulePullback f.toLRSHom.toShHom).obj ((modulePullback g.toLRSHom.toShHom).obj N) := by
  subst hfg
  exact (RingedSpaceModuleAdjunction.modulePullbackComp
    f.toLRSHom.toShHom g.toLRSHom.toShHom).app N

/-- **A base change along which the module becomes free satisfies the descent condition.** If the
pullback of `E` to `X ×_S T` is free on `r` generators, then the free module on `r` generators on
`T` witnesses `AlgebraicGeometry.DescendsFromBase f E g`, because pullback carries a free module
to the free module on the same index type.

This is the implication by which the fibrewise hypothesis of Stacks Tag 0EX7 puts every residue
field of the base in the descent locus. -/
theorem descendsFromBase_of_nonempty_iso_free {X S : Scheme.{u}} (f : X ⟶ S)
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {T : Scheme.{u}} (g : T ⟶ S) (r : ℕ)
    (h : Nonempty ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E ≅
      _root_.SheafOfModules.free (ULift.{u} (Fin r)))) :
    DescendsFromBase f E g :=
  ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)),
    SheafOfModules.isFiniteLocallyFree_free T r,
    ⟨modulePullbackObjFreeIso (pullback.snd f g).toLRSHom.toShHom (ULift.{u} (Fin r)) ≪≫
      h.some.symm⟩⟩

namespace IsDescentLocus

variable {X S : Scheme.{u}} {f : X ⟶ S}
  {E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} {Z : Over S}

/-- **A descent locus containing every residue field of the base is surjective onto it.** If the
module descends along the base change `Spec κ(s) ⟶ S` for every point `s`, that base change
factors through the locus, and the image of the closed point of `Spec κ(s)` is `s`. -/
theorem range_hom_eq_univ_of_forall_descendsFromBase (hZ : IsDescentLocus f E Z)
    (hs : ∀ s : S, DescendsFromBase f E (S.fromSpecResidueField s)) :
    Set.range Z.hom = Set.univ := by
  refine Set.eq_univ_of_forall fun s ↦ ?_
  obtain ⟨k, hk⟩ := (hZ.factorsThrough_iff (S.fromSpecResidueField s)).2 (hs s)
  refine ⟨k (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
  have hk' := congrArg
    (fun m : Spec (S.residueField s) ⟶ S => m (IsLocalRing.closedPoint (S.residueField s))) hk
  calc Z.hom (k (IsLocalRing.closedPoint (S.residueField s)))
      = (k ≫ Z.hom) (IsLocalRing.closedPoint (S.residueField s)) :=
        (Scheme.Hom.comp_apply k Z.hom _).symm
    _ = S.fromSpecResidueField s (IsLocalRing.closedPoint (S.residueField s)) := hk'
    _ = s := Scheme.fromSpecResidueField_apply s _

/-- **Over a reduced base, a descent locus containing every residue field is the whole base.**
The locus is immersed with full image, hence a surjective closed immersion, and a surjective
closed immersion into a reduced scheme is an isomorphism.

Reducedness is used only here, and it is the hypothesis of Stacks Tag 0EX7 that cannot be
dropped: a surjective closed immersion into a non-reduced scheme need not be an isomorphism. -/
theorem isIso_hom_of_forall_descendsFromBase (hZ : IsDescentLocus f E Z) [IsReduced S]
    (hs : ∀ s : S, DescendsFromBase f E (S.fromSpecResidueField s)) :
    IsIso Z.hom := by
  have hrange := hZ.range_hom_eq_univ_of_forall_descendsFromBase hs
  have := hZ.isImmersion
  have : IsClosedImmersion Z.hom :=
    IsClosedImmersion.of_isPreimmersion Z.hom (hrange ▸ isClosed_univ)
  have : Surjective Z.hom := ⟨Set.range_eq_univ.mp hrange⟩
  exact isIso_of_isClosedImmersion_of_surjective Z.hom

/-- **A module descends from the base when its descent locus is the whole base.** An inverse of
the structure morphism of the locus factors the identity of `S` through it, so the descent
condition holds along `𝟙 S`; transporting the resulting isomorphism along the projection
`X ×_S S ⟶ X`, which is an isomorphism, exhibits `E` as the pullback of a finite locally free
module on `S`. -/
theorem exists_finiteLocallyFree_iso_of_isIso_hom (hZ : IsDescentLocus f E Z) [IsIso Z.hom] :
    ∃ N : _root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback f.toLRSHom.toShHom).obj N ≅ E) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := (hZ.factorsThrough_iff (𝟙 S)).1 ⟨inv Z.hom, by simp⟩
  refine ⟨N, hN, ?_⟩
  let p : pullback f (𝟙 S) ⟶ X := pullback.fst f (𝟙 S)
  let q : pullback f (𝟙 S) ⟶ S := pullback.snd f (𝟙 S)
  have hpf : p ≫ f = q := by
    change pullback.fst f (𝟙 S) ≫ f = pullback.snd f (𝟙 S)
    simpa using (pullback.condition : pullback.fst f (𝟙 S) ≫ f = pullback.snd f (𝟙 S) ≫ 𝟙 S)
  have hiq : inv p ≫ q = f := by rw [← hpf, IsIso.inv_hom_id_assoc]
  have hip : inv p ≫ p = 𝟙 X := IsIso.inv_hom_id p
  exact ⟨modulePullbackIsoOfComp (inv p) q f hiq N ≪≫
    (modulePullback (inv p).toLRSHom.toShHom).mapIso e ≪≫
    (modulePullbackIsoOfComp (inv p) p (𝟙 X) hip E).symm ≪≫
    (RingedSpaceModuleAdjunction.modulePullbackId X.toRingedSpace).app E⟩

/-- **Stacks Tag 0EX7 for a given descent locus.** A finite locally free module whose
restriction to every fibre of `f` is free of finite rank is the pullback of a finite locally free
module on the reduced base `S`, provided the descent condition for it is represented by `Z`. -/
theorem exists_finiteLocallyFree_iso_of_fiberwiseFree (hZ : IsDescentLocus f E Z) [IsReduced S]
    (hfiber : ∀ s : S, ∃ r : ℕ,
      Nonempty ((modulePullback
          (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r)))) :
    ∃ N : _root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback f.toLRSHom.toShHom).obj N ≅ E) :=
  have hs : ∀ s : S, DescendsFromBase f E (S.fromSpecResidueField s) := fun s ↦
    (hfiber s).elim fun r h ↦ descendsFromBase_of_nonempty_iso_free f E _ r h
  have := hZ.isIso_hom_of_forall_descendsFromBase hs
  hZ.exists_finiteLocallyFree_iso_of_isIso_hom

end IsDescentLocus

/-- **A module pulled back from the base has a descent locus, namely the base itself.** Every
base change `g : T ⟶ S` then satisfies the descent condition for `E`, witnessed on `T` by the
pullback of `N` along `g`.

This records that the representability hypothesis of
`AlgebraicGeometry.exists_finiteLocallyFree_iso_of_fiberwiseFree` is implied by its conclusion,
so assuming it is weaker than assuming what is to be proved. -/
theorem hasDescentLocus_of_exists_finiteLocallyFree_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (N : _root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hN : ∀ T : Scheme.{u}, ∀ g : T ⟶ S,
      SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((modulePullback g.toLRSHom.toShHom).obj N))
    (e : (modulePullback f.toLRSHom.toShHom).obj N ≅ E) :
    HasDescentLocus f E := by
  refine ⟨Over.mk (𝟙 S), ?_, ?_, ?_⟩
  · dsimp; infer_instance
  · exact (⟨inferInstance, inferInstance, inferInstance⟩ : FinitePresentation (𝟙 S))
  · intro T g
    refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨g, Category.comp_id g⟩⟩
    refine ⟨(modulePullback g.toLRSHom.toShHom).obj N, hN T g, ?_⟩
    have hgf : pullback.snd f g ≫ g = pullback.fst f g ≫ f := pullback.condition.symm
    exact ⟨(modulePullbackIsoOfComp _ g _ hgf N).symm ≪≫
      modulePullbackIsoOfComp (pullback.fst f g) f _ rfl N ≪≫
      (modulePullback (pullback.fst f g).toLRSHom.toShHom).mapIso e⟩

/-- **Stacks Tag 0EX7, reduced to representability of the descent condition.** A finite locally
free module on `X` whose restriction to every fibre of `f` is free of finite rank is the pullback
of a finite locally free module on the reduced base `S`, provided the descent condition for it is
represented — that is, provided the conclusion of Stacks Tag 0BDP holds for `f` and `E`.

Tag 0BDP's hypotheses on `f` — flatness, properness, finite presentation, and invariance of the
structure sheaf under pushforward along every base change — enter only through that
representability, and so do not appear. -/
@[stacks 0EX7 "assuming the representability of the descent locus of Tag 0BDP"]
theorem exists_finiteLocallyFree_iso_of_fiberwiseFree {X S : Scheme.{u}} (f : X ⟶ S)
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (h0BDP : HasDescentLocus f E) [IsReduced S]
    (hfiber : ∀ s : S, ∃ r : ℕ,
      Nonempty ((modulePullback
          (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r)))) :
    ∃ N : _root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback f.toLRSHom.toShHom).obj N ≅ E) :=
  (isDescentLocus_descentLocus f E h0BDP).exists_finiteLocallyFree_iso_of_fiberwiseFree hfiber

-- **Stacks Tag 0EX7**, stated with its hypotheses copied from the source and with
-- representability of the descent condition -- the conclusion of Stacks Tag 0BDP, which is not
-- proved in this library -- added as the one extra hypothesis `h0BDP`.
--
-- The flatness, properness and finite presentation of `f`, the invariance of its direct image of
-- the structure sheaf under arbitrary base change, and the finite local freeness of `E` are
-- carried unchanged from the tag. They are exactly the hypotheses of Tag 0BDP, and once `h0BDP`
-- is assumed none of them is used again, which is why this is an `example`: a named declaration
-- would be reported by the `unusedArguments` linter.
example {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] (_hfp : FinitePresentation f)
    (_hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (_hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (hfiber : ∀ s : S, ∃ r : ℕ,
      Nonempty ((modulePullback
          (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))))
    [IsReduced S] (h0BDP : HasDescentLocus f E) :
    ∃ N : _root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback f.toLRSHom.toShHom).obj N ≅ E) :=
  exists_finiteLocallyFree_iso_of_fiberwiseFree f E h0BDP hfiber

end AlgebraicGeometry

end
