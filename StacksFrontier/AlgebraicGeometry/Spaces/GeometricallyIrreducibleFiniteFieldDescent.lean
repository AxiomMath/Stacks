module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoprimeDegreeSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.FieldBaseChangeSchemeModels
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.RingTheory.FiniteField.PointsOfCoprimeDegree
public import StacksFrontier.RingTheory.GeometricallyIrreducible.DirectedUnionFiniteType
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically irreducible extensions of a finite field

Let `k` be a finite field and `K/k` a geometrically irreducible field extension. This file
formalizes Stacks Remark 0BA7:

1. `K` is the directed union, hence the limit, of geometrically irreducible finitely generated
   `k`-subalgebras `A`;
2. for each geometrically irreducible `k`-algebra `A` of finite type there is, for every `n ≫ 0`, a
   `k`-algebra map `A → k'` with `[k' : k] = n` (the estimates of Lang and Weil);
3. a quasi-separated algebraic space `X` over `k` such that `X_K` is a scheme is a scheme.

Part (3) runs the argument of Stacks 0B85 for a finite ground field. That argument only uses
that every finitely generated subalgebra of `K` maps to finite extensions of `k` of every degree
prime to a given `d`, which part (2) provides. The general statement with that hypothesis is
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_of_forall_coprime`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_of_forall_coprime`:
  descent of schemes along `K/k` for a finite field `k`, from points of coprime degrees.
* `Space.isRepresentable_of_isRepresentable_baseChange_of_isGeometricallyIrreducible`:
  part (3).
* `Algebra.IsGeometricallyIrreducible.finiteField_remark`: **Stacks 0BA7**, all three parts.

## Implementation notes

The base change `X_K` is the restriction of `X` to the big fppf site of `Spec K`, along
`Spec K ⟶ Spec k`; the site is assumed to contain `Spec K`. The proof reduces to quasi-compact
open subspaces, finds a finitely generated subalgebra `A ⊆ K` with `X_A` a scheme (Stacks 07SR),
replaces `X` by a model of finite presentation over `k` (Stacks 09NS), and concludes with
`AlgebraicGeometry.Space.isRepresentable_of_forall_coprime_algHom_of_isRepresentable_baseChange`.

## References

* [Stacks Project, Tag 0BA7](https://stacks.math.columbia.edu/tag/0BA7)
* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Module

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-compact Zariski covers.** Every algebraic space has a Zariski covering by
quasi-compact open subspaces: the members of the covering of
`AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas` have affine étale atlases. -/
theorem exists_isZariskiCover_isQuasiCompactSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (V : I → Subfunctor F), IsZariskiCover B S hS I V ∧
      ∀ i, IsQuasiCompactSpace B S hS (V i).toFunctor := by
  obtain ⟨I, V, hcover, hatlas⟩ := exists_zariski_cover_affine_etale_atlas B S hS F hF
  refine ⟨I, V, hcover, fun i => ?_⟩
  obtain ⟨U, f, -, hU, hsurj, hetale, -⟩ := hatlas i
  exact ⟨U, f, inferInstance, hsurj, (isEtale_iff_presheaf_of_yoneda B S hS f).2 hetale⟩

/-- **Quasi-separated over a quasi-separated base is absolutely quasi-separated.** -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparatedOver [QuasiSeparatedSpace S]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsQuasiSeparatedOver B S hS F) :
    IsAbsolutelyQuasiSeparated B S hS B.contains_terminal F :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hF
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ B.contains_terminal
      ⟨Over.mk (𝟙 (B.obj hS)), inferInstanceAs (QuasiSeparatedSpace S),
        ⟨Functor.RepresentableBy.yoneda _⟩⟩)
    (isQuasiSeparated_of_isQuasiSeparatedOver B S hS hqs
      ((isTerminal_yoneda_obj_base B S hS).from F))

/-- **Base change of an open subspace.** If the base change of `F` along `T ⟶ S` is a scheme,
so is that of every open subspace of `F`: base change preserves open immersions, and an open
immersion into a scheme has scheme source. -/
theorem isRepresentable_relocalizeRestrict_of_isOpenSubspace {T : Scheme.{u}}
    (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : Subfunctor F) (hV : IsOpenSubspace B S hS V)
    (hFT : ((OverShriek.relocalizeRestrict g).obj F).IsRepresentable) :
    ((OverShriek.relocalizeRestrict g).obj V.toFunctor).IsRepresentable :=
  have := hFT
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_inverseImage_relocalizeRestrict_map B T S hT hS g
      (@AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance hV.2).1

end General

section OverField

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **Descent of schemes along a field extension of a finite field, from points of coprime
degrees.** Let `k` be finite and `K/k` a field extension such that every finitely generated
`k`-subalgebra of `K` maps, for every `d > 0`, to a finite extension of `k` of degree prime to
`d`. If `X` is a quasi-separated algebraic space over `k` and `X_K` is a scheme, then `X` is a
scheme. -/
theorem isRepresentable_of_isRepresentable_baseChange_of_forall_coprime [Finite k] (K : Type u)
    [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) {F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hqs : IsQuasiSeparatedOver B (Spec (.of k)) hk F)
    (hpts : ∀ A : Subalgebra k K, A.FG → ∀ d : ℕ, 0 < d →
      ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
        Nat.Coprime (finrank k L) d ∧ Nonempty (A →ₐ[k] L))
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        B.obj hK ⟶ B.obj hk)).obj F).IsRepresentable) :
    F.IsRepresentable := by
  obtain ⟨I, V, hcover, hqc⟩ := exists_isZariskiCover_isQuasiCompactSpace B _ hk hF
  refine isRepresentable_of_isZariskiCover B _ hk F hF I V hcover fun i => ?_
  have hVi := (hcover.1 i).1
  have hVqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedOver B _ hk hVi
    (isQuasiSeparatedOver_subfunctor B _ hk hqs (V i))
  have hVK :=
    isRepresentable_relocalizeRestrict_of_isOpenSubspace B _ hk hK _ (V i) (hcover.1 i) hbase
  obtain ⟨A, hA, hAs, hVA⟩ := exists_fg_isRepresentable_baseChange_subalgebra k K B hk hK _ hVi
    (hqc i) hVqs hVK
  obtain ⟨B', -, hk', hA', G, hG, f, hfp, hGA, hback⟩ :=
    exists_finitePresentation_model_of_isRepresentable_baseChange_affine k B hk _ hVi (hqc i) hVqs A
      hAs hVA
  exact hback (isRepresentable_of_forall_coprime_algHom_of_isRepresentable_baseChange k B' hk' A
    (hpts A hA) hA' hG f hfp hGA)

/-- **Stacks 0BA7, part (3).** Let `k` be a finite field and `K/k` a geometrically irreducible
field extension. A quasi-separated algebraic space `X` over `k` such that `X_K` is a scheme is a
scheme. -/
theorem isRepresentable_of_isRepresentable_baseChange_of_isGeometricallyIrreducible [Finite k]
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsGeometricallyIrreducible k K)
    (hK' : B.Contains (Spec (.of K))) {F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hqs : IsQuasiSeparatedOver B (Spec (.of k)) hk F)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        B.obj hK' ⟶ B.obj hk)).obj F).IsRepresentable) :
    F.IsRepresentable :=
  isRepresentable_of_isRepresentable_baseChange_of_forall_coprime k B hk K hK' hF hqs
    (fun A hA d hd => hK.exists_finrank_coprime_algHom_of_fg A hA d hd) hbase

end OverField

end AlgebraicGeometry.Space

namespace Algebra.IsGeometricallyIrreducible

open AlgebraicGeometry AlgebraicGeometry.Space

/-- **Stacks 0BA7.** Let `k` be a finite field and `K/k` a geometrically irreducible field
extension.
1. `K` is the directed union of geometrically irreducible `k`-subalgebras of finite type.
2. For every geometrically irreducible `k`-algebra `A` of finite type there is `N` such that
   for every finite extension `k'/k` of degree `n ≥ N` there is a `k`-algebra map `A → k'`.
3. If `X` is a quasi-separated algebraic space over `k` and `X_K` is a scheme, then `X` is a
   scheme. -/
@[stacks 0BA7]
theorem finiteField_remark (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
    (hK : Algebra.IsGeometricallyIrreducible k K) :
    (∃ (ι : Type u) (A : ι → Subalgebra k K), Directed (· ≤ ·) A ∧ (⨆ i, A i) = ⊤ ∧
      ∀ i, Algebra.FiniteType k (A i) ∧ Algebra.IsGeometricallyIrreducible k (A i)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      Algebra.IsGeometricallyIrreducible k A →
      ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'],
        N ≤ finrank k k' → Nonempty (A →ₐ[k] k')) ∧
    (∀ (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k))) (hK' : B.Contains (Spec (.of K)))
      (F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B (Spec (.of k)) hk F →
      IsQuasiSeparatedOver B (Spec (.of k)) hk F →
      ((OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          B.obj hK' ⟶ B.obj hk)).obj F).IsRepresentable →
      F.IsRepresentable) :=
  ⟨hK.exists_directed_fg_subalgebras,
    fun A _ _ _ hA =>
      Algebra.exists_forall_nonempty_algHom_of_le_finrank_of_isGeometricallyIrreducible k A hA,
    fun B hk hK' _ hF hqs hbase =>
      isRepresentable_of_isRepresentable_baseChange_of_isGeometricallyIrreducible k B hk K hK hK'
        hF hqs hbase⟩

end Algebra.IsGeometricallyIrreducible

end
