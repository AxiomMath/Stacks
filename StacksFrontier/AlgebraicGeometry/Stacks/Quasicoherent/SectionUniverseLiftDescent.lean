module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Lowering the universe of the sections by an arbitrary amount

Raising the universe of the sections of a sheaf of modules by an *arbitrary* amount neither
creates nor destroys a global presentation in the sense of Stacks 03DE(6), hence neither creates
nor destroys quasi-coherence in the sense of Stacks 03DL(6).  The upward direction is
`SheafOfModules.hasGlobalPresentation_uliftForPresentation'`; this file supplies the downward one.

At the lifting amount `max u v r`, with `u` and `v` the universes of the objects and the morphisms
of the site and `r` that of the coefficient rings, the downward direction is isomorphism
bookkeeping: a global presentation of a module with sections in `Type m` is indexed by types in
`Type (max u v r m)`, and such a lift leaves that universe unchanged, so the two statements have
the same index types and the same presenting diagram.  That case is
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation`.

At a general amount `t` the two statements are *not* in the same universe.  A presentation of the
lift is indexed by types in `Type (max u v r t m)`, which is strictly larger than
`Type (max u v r m)` as soon as `t` is not contained in `max u v r m`, so the index types must
genuinely be shrunk; on a big site, where the objects lie one universe above the sections, no
such shrinking of an arbitrary type is available.  What saves the statement is that the index
types do not have to be shrunk, only their *images*: the generators named by the big index type
are morphisms in a category whose sections already lie in `Type (max u v r m)`, so the set of
generators actually used is a type in that universe on the nose, with no size hypothesis
anywhere.

## Main results

* `SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`: **a global presentation of the
  universe lift of the sections, by an arbitrary amount, is one of the module itself.**  Together
  with `SheafOfModules.hasGlobalPresentation_uliftForPresentation'` this makes having a global
  presentation invariant under raising the universe of the sections by any amount.
* `SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`: the same for quasi-coherence
  in the sense of Stacks 03DL(6).

## Implementation notes

Write `V` for `max u v r m`, the universe in which a global presentation of the module is
indexed, `W` for `max u v r t m`, the one in which a global presentation of the lift is indexed,
and `L` for the universe lift of the sections from `V` to `W`.  The hypothesis presents the lift
of the module as a cokernel of a map between `W`-indexed coproducts of copies of the structure
sheaf, and `SheafOfModules.uliftForPresentationCompIso` identifies both the structure sheaf and
the presented module appearing there with the images under `L` of their counterparts at `V`.

The generators are then read off downstairs: `L` is full, by
`SheafOfModules.full_uliftForPresentationFunctor`, so each composite of a cofan injection with
the presenting epimorphism is `L` of a morphism from the structure sheaf to the module at `V`,
and the *range* of the resulting family is a subtype of a hom set of `SheafOfModules.{V} R`,
which is a type in `Type V`.  Coproducts of `Type V`-indexed families exist in that category
without hypothesis, since `V` contains the site and therefore
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat` apply at `V`.

Restricting to the range rather than to all sections is what makes the comparison map from the
given coproduct to the image under `L` of the new one a *split* epimorphism: a splitting picks,
for each generator in the range, one index of the big type that produced it.  Splitness moves the
cokernel across the factorisation, and then fullness and faithfulness of `L` carry the cokernel
diagram down to `V`.  The relations are shrunk the same way, from the second cofan, so no kernel
and no exactness of the lift is needed.

This is the shape of
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`, which shrinks the
index types all the way to the universe of the coefficient rings and therefore does need a
smallness hypothesis and the free sheaves of modules.  Here the target universe already contains
the site, so the hom sets are the right size on the nose and abstract coproducts suffice.

Nothing here carries a `stacks` attribute: it is the bookkeeping that puts two universes of one
statement of Stacks 03DE(6) in bijection, not a result of the source.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A global presentation of the universe lift of the sections, by an arbitrary amount, is one
of the module itself.**  At the amount `max u v r` this is
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation`, where the two statements are
indexed by the same universe; here the index types must be shrunk from `max u v r t m` to
`max u v r m`, and what makes that possible with no size hypothesis is that only the *image* of
an index type in a hom set of `SheafOfModules.{max u v r m} R` is needed, and such a hom set
already lies in `Type (max u v r m)`.

The converse is `SheafOfModules.hasGlobalPresentation_uliftForPresentation'`. -/
theorem HasGlobalPresentation.of_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, t} M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  have hs₁ : HasSheafify J AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
  have hw₁ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
  have hs₂ : HasSheafify J AddCommGrpCat.{max u v r t m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r t m, v, u} J
  have hw₂ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r t m, u, v} J
  have hpc : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)) :=
    preservesColimitsOfSize_uliftForPresentationFunctor.{u, v, r, max u v m, t}
  set L := uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R) with hL
  set unitV := uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) with hunitV
  set MV := uliftForPresentation.{u, v, r, m, max u v r} M with hMV
  let γ : L.obj unitV ≅ uliftForPresentation.{u, v, r, r, max u v t m} (SheafOfModules.unit R) :=
    uliftForPresentationCompIso.{u, v, r, r, max u v m, t} (SheafOfModules.unit R)
  let δ : L.obj MV ≅ uliftForPresentation.{u, v, r, max t m, max u v r}
      (uliftForPresentation.{u, v, r, m, t} M) :=
    uliftForPresentationCompIso.{u, v, r, m, max u v r, t} M ≪≫
      (uliftForPresentationCompIso.{u, v, r, m, t, max u v r} M).symm
  -- The presenting epimorphism, read as a map into the image under `L` of the module at `V`.
  set b₀ : P ⟶ L.obj MV := b ≫ δ.inv with hb₀def
  have hab₀ : a ≫ b₀ = 0 := by rw [hb₀def, ← Category.assoc, hab, zero_comp]
  have hb₀ : IsColimit (CokernelCofork.ofπ b₀ hab₀) := hb.ofIsoColimit (Cofork.ext δ.symm rfl)
  -- The generators: the image in a hom set at `V` of the big index type of the presentation.
  set g : I → (unitV ⟶ MV) := fun i ↦ L.preimage (γ.hom ≫ ι i ≫ b₀) with hgdef
  have hg : ∀ i, L.map (g i) = γ.hom ≫ ι i ≫ b₀ := fun i ↦ L.map_preimage _
  set A : Set (unitV ⟶ MV) := Set.range g with hAdef
  set fA : ↥A → SheafOfModules.{max u v r m} R := fun _ ↦ unitV with hfA
  have hmemA : ∀ i, g i ∈ A := fun i ↦ ⟨i, rfl⟩
  set π : ∐ fA ⟶ MV := Sigma.desc (fun s ↦ s.1) with hπdef
  have hπfac : ∀ s : ↥A, Sigma.ι fA s ≫ π = s.1 := fun s ↦ Sigma.ι_desc _ _
  have hPA : IsColimit (Cofan.mk (∐ fA) (Sigma.ι fA)) := coproductIsCoproduct fA
  have hLPA : IsColimit (Cofan.mk (L.obj (∐ fA))
      (fun s ↦ γ.inv ≫ L.map (Sigma.ι fA s))) :=
    isColimit_cofan_comp_iso γ.symm _ (isColimitCofanMkObjOfIsColimit L fA _ hPA)
  -- The comparison map out of the given coproduct, and the splitting its index set affords.
  set d : P ⟶ L.obj (∐ fA) :=
    Cofan.IsColimit.desc hP (fun i ↦ γ.inv ≫ L.map (Sigma.ι fA ⟨g i, hmemA i⟩)) with hddef
  have hdfac : ∀ i, ι i ≫ d = γ.inv ≫ L.map (Sigma.ι fA ⟨g i, hmemA i⟩) := by
    intro i
    rw [hddef]
    exact Cofan.IsColimit.fac hP _ i
  have hdb : d ≫ L.map π = b₀ := by
    refine Cofan.IsColimit.hom_ext hP _ _ fun i ↦ ?_
    rw [Limits.cofan_mk_inj, ← Category.assoc, hdfac i, Category.assoc, ← L.map_comp,
      hπfac ⟨g i, hmemA i⟩, hg i]
    simp
  set j : L.obj (∐ fA) ⟶ P :=
    Cofan.IsColimit.desc hLPA (fun s ↦ ι (Set.mem_range.mp s.2).choose) with hjdef
  have hjfac : ∀ s : ↥A, (γ.inv ≫ L.map (Sigma.ι fA s)) ≫ j =
      ι (Set.mem_range.mp s.2).choose := by
    intro s
    rw [hjdef]
    exact Cofan.IsColimit.fac hLPA _ s
  have hjd : j ≫ d = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hLPA _ _ fun s ↦ ?_
    have hs : (⟨g (Set.mem_range.mp s.2).choose, hmemA _⟩ : ↥A) = s :=
      Subtype.ext (Set.mem_range.mp s.2).choose_spec
    rw [Limits.cofan_mk_inj, ← Category.assoc, hjfac s, hdfac, hs]
    exact (Category.comp_id _).symm
  -- The relations: the image in a hom set at `V` of the second index type.
  set sk : K → (unitV ⟶ ∐ fA) := fun k ↦ L.preimage (γ.hom ≫ κ k ≫ a ≫ d) with hskdef
  have hskL : ∀ k, L.map (sk k) = γ.hom ≫ κ k ≫ a ≫ d := fun k ↦ L.map_preimage _
  have hskπ : ∀ k, sk k ≫ π = 0 := by
    intro k
    refine L.map_injective ?_
    rw [L.map_comp, hskL, Functor.map_zero]
    simp only [Category.assoc]
    rw [hdb, hab₀, comp_zero, comp_zero]
  set B : Set (unitV ⟶ ∐ fA) := Set.range sk with hBdef
  set fB : ↥B → SheafOfModules.{max u v r m} R := fun _ ↦ unitV with hfB
  have hmemB : ∀ k, sk k ∈ B := fun k ↦ ⟨k, rfl⟩
  set α : ∐ fB ⟶ ∐ fA := Sigma.desc (fun s ↦ s.1) with hαdef
  have hαfac : ∀ s : ↥B, Sigma.ι fB s ≫ α = s.1 := fun s ↦ Sigma.ι_desc _ _
  have hQB : IsColimit (Cofan.mk (∐ fB) (Sigma.ι fB)) := coproductIsCoproduct fB
  have hαπ : α ≫ π = 0 := by
    refine Cofan.IsColimit.hom_ext hQB _ _ fun s ↦ ?_
    obtain ⟨k, hk⟩ := s.2
    rw [Limits.cofan_mk_inj, ← Category.assoc, hαfac s, comp_zero, ← hk, hskπ k]
  set ε : Q ⟶ L.obj (∐ fB) :=
    Cofan.IsColimit.desc hQ (fun k ↦ γ.inv ≫ L.map (Sigma.ι fB ⟨sk k, hmemB k⟩)) with hεdef
  have hεfac : ∀ k, κ k ≫ ε = γ.inv ≫ L.map (Sigma.ι fB ⟨sk k, hmemB k⟩) := by
    intro k
    rw [hεdef]
    exact Cofan.IsColimit.fac hQ _ k
  have hεα : ε ≫ L.map α = a ≫ d := by
    refine Cofan.IsColimit.hom_ext hQ _ _ fun k ↦ ?_
    simp only [Limits.cofan_mk_inj, ← Category.assoc]
    rw [hεfac k, Category.assoc, ← L.map_comp, hαfac ⟨sk k, hmemB k⟩, hskL k]
    simp
  -- Both the lift of `π` and `π` itself are epimorphisms, because `b` is.
  have hbepi : Epi b₀ := by
    have hbe : Epi b := Cofork.IsColimit.epi hb
    rw [hb₀def]
    infer_instance
  have hLπepi : Epi (L.map π) := by
    have : Epi (d ≫ L.map π) := by rw [hdb]; exact hbepi
    exact epi_of_epi d _
  have hπepi : Epi π := ⟨fun {_} p q hpq ↦ L.map_injective
    ((cancel_epi (L.map π)).mp (by rw [← L.map_comp, ← L.map_comp, hpq]))⟩
  -- The lift of `π` is a cokernel of the lift of `α`, because `d` is a split epimorphism.
  have hLα : L.map α ≫ L.map π = 0 := by rw [← L.map_comp, hαπ, Functor.map_zero]
  have hLcol : IsColimit (CokernelCofork.ofπ (L.map π) hLα) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} k hk ↦ ?_
    have h0 : a ≫ d ≫ k = 0 := by
      rw [← Category.assoc, ← hεα, Category.assoc, hk, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' hb₀ (d ≫ k) h0
    have hn' : b₀ ≫ n = d ≫ k := hn
    refine ⟨n, ?_⟩
    have e1 : L.map π ≫ n = j ≫ d ≫ L.map π ≫ n := by
      rw [← Category.assoc j, hjd, Category.id_comp]
    have e2 : j ≫ d ≫ L.map π ≫ n = j ≫ d ≫ k := by
      rw [← Category.assoc d, hdb, hn']
    have e3 : j ≫ d ≫ k = k := by rw [← Category.assoc, hjd, Category.id_comp]
    rw [e1, e2, e3]
  -- The universe lift is full and faithful, so that cokernel diagram descends.
  have hcol : IsColimit (CokernelCofork.ofπ π hαπ) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} k hk ↦ ?_
    have hk' : L.map α ≫ L.map k = 0 := by rw [← L.map_comp, hk, Functor.map_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' hLcol (L.map k) hk'
    have hn' : L.map π ≫ n = L.map k := hn
    refine ⟨L.preimage n, L.map_injective ?_⟩
    rw [L.map_comp, L.map_preimage]
    exact hn'
  exact ⟨↥A, ↥B, ∐ fA, ∐ fB, Sigma.ι fA, Sigma.ι fB, ⟨hPA⟩, ⟨hQB⟩, α, π, hαπ, ⟨hcol⟩⟩

/-- **Quasi-coherence of the universe lift of the sections, by an arbitrary amount, is
quasi-coherence of the module itself.**  Raising the universe of the sections commutes with
restriction to a slice site, so a covering on whose members the lift is globally presented serves
for the module as well.  The converse is
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`. -/
theorem IsQuasicoherentOnSite.of_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, t} M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
    exact ⟨I, V, f, hcover, fun i ↦
      HasGlobalPresentation.of_uliftForPresentation'.{max u v, v, r, m, t} (hpres i)⟩

end SheafOfModules

end
