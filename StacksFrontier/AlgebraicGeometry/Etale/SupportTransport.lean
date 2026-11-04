module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSectionsClopen

/-!
# Transport of the support of a section

Let `B` be a big étale site containing a scheme `S` and let `F` be an abelian sheaf on the
small étale site of `S` inside `B`. The support of a section of `F` is unchanged by an
isomorphism of abelian sheaves, and it is carried along the induced homeomorphism by an
isomorphism of the site. A section supported inside the image of an open immersion of the site
is determined by its restriction there.

## Main results

* `AlgebraicGeometry.SmallEtale.supportSection_neg` — a section and its negative have the same
  support.
* `AlgebraicGeometry.SmallEtale.zeroOpen_sheafIso` and
  `AlgebraicGeometry.SmallEtale.supportSection_sheafIso` — an isomorphism of abelian sheaves
  preserves the maximal zero open and the support.
* `AlgebraicGeometry.SmallEtale.supportSection_map_inv` — an isomorphism of the site carries
  the support of a section to the support of its transport.
* `AlgebraicGeometry.SmallEtale.eq_of_map_eq_of_supportSection_subset` — two sections supported
  inside the image of an open immersion of the site which restrict to the same section there
  are equal.

## Implementation notes

Both transport statements reduce to the description of the support of a restricted section as
the inverse image of the support, `AlgebraicGeometry.SmallEtale.supportSection_map`: for an
isomorphism of the site the inverse image along the inverse is the image along the isomorphism,
and for an isomorphism of sheaves the two inclusions of
`AlgebraicGeometry.SmallEtale.supportSection_map_subset` are mutually inverse.

The last statement is the only place where the sheaf axiom enters: the difference of the two
sections restricts to zero on the open, so its support is disjoint from that open, while being
contained in it; hence the support is empty and the difference vanishes.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 04FT](https://stacks.math.columbia.edu/tag/04FT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sheaf

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- A section and its negative vanish on the same Zariski opens, hence have the same
support. -/
public theorem supportSection_neg (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    supportSection B S hS F U (-s) = supportSection B S hS F U s := by
  unfold supportSection
  rw [zeroOpen_neg]

end Sheaf

section SheafIso

variable {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}}

/-- An isomorphism of abelian sheaves preserves the support of a section: each of its two
directions cannot enlarge a support, and they are mutually inverse. -/
public theorem supportSection_sheafIso (e : F ≅ G) (U : SmallEtale B S hS)
    (s : F.obj.obj (op U)) :
    supportSection B S hS G U (e.hom.hom.app (op U) s) = supportSection B S hS F U s := by
  refine Set.Subset.antisymm (supportSection_map_subset B S hS F G e.hom U s) ?_
  have h := supportSection_map_subset B S hS G F e.inv U (e.hom.hom.app (op U) s)
  have heval : e.inv.hom.app (op U) (e.hom.hom.app (op U) s) = s :=
    congrArg (fun φ : F ⟶ F => φ.hom.app (op U) s) e.hom_inv_id
  rwa [heval] at h

/-- An isomorphism of abelian sheaves preserves the maximal Zariski open on which a section
vanishes. -/
public theorem zeroOpen_sheafIso (e : F ≅ G) (U : SmallEtale B S hS)
    (s : F.obj.obj (op U)) :
    zeroOpen B S hS G U (e.hom.hom.app (op U) s) = zeroOpen B S hS F U s := by
  apply TopologicalSpace.Opens.ext
  have h := supportSection_sheafIso B S hS e U s
  unfold supportSection at h
  exact compl_injective h

end SheafIso

section SiteIso

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- For an isomorphism `e : U ≅ V` in the small étale site, the map of underlying spaces induced by
`e.inv` is a left inverse of the one induced by `e.hom`. -/
theorem toScheme_map_inv_hom_apply {U V : SmallEtale B S hS} (e : U ≅ V)
    (x : (SmallEtale.toScheme B S hS).obj U) :
    ((SmallEtale.toScheme B S hS).map e.inv).base
        (((SmallEtale.toScheme B S hS).map e.hom).base x) = x :=
  congrArg (fun g : (SmallEtale.toScheme B S hS).obj U ⟶ _ => g.base x)
    ((SmallEtale.toScheme B S hS).mapIso e).hom_inv_id

/-- For an isomorphism `e : U ≅ V` in the small étale site, the map of underlying spaces induced by
`e.hom` is a left inverse of the one induced by `e.inv`. -/
theorem toScheme_map_hom_inv_apply {U V : SmallEtale B S hS} (e : U ≅ V)
    (x : (SmallEtale.toScheme B S hS).obj V) :
    ((SmallEtale.toScheme B S hS).map e.hom).base
        (((SmallEtale.toScheme B S hS).map e.inv).base x) = x :=
  toScheme_map_inv_hom_apply B S hS e.symm x

/-- Transporting a section along an isomorphism of the small étale site transports its support
along the induced homeomorphism. -/
public theorem supportSection_map_inv {U V : SmallEtale B S hS} (e : U ≅ V)
    (s : F.obj.obj (op U)) :
    supportSection B S hS F V (F.obj.map e.inv.op s) =
      ((SmallEtale.toScheme B S hS).map e.hom).base '' supportSection B S hS F U s := by
  rw [supportSection_map B S hS F U V e.inv s]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  refine ⟨fun hx => ⟨_, hx, toScheme_map_hom_inv_apply B S hS e x⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  rwa [toScheme_map_inv_hom_apply]

end SiteIso

section Determined

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- Two sections supported inside the image of an open immersion of the small étale site which
restrict to the same section along it are equal: their difference is supported inside that
image and restricts to zero there, so its support is empty. -/
public theorem eq_of_map_eq_of_supportSection_subset {U V : SmallEtale B S hS} (e : V ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map e)]
    (s t : F.obj.obj (op U))
    (hs : supportSection B S hS F U s ⊆ Set.range ((SmallEtale.toScheme B S hS).map e).base)
    (ht : supportSection B S hS F U t ⊆ Set.range ((SmallEtale.toScheme B S hS).map e).base)
    (hres : F.obj.map e.op s = F.obj.map e.op t) : s = t := by
  have hzero : F.obj.map e.op (s - t) = 0 := by rw [map_sub, hres, sub_self]
  have hsub : supportSection B S hS F U (s - t) ⊆
      Set.range ((SmallEtale.toScheme B S hS).map e).base := by
    intro x hx
    rw [sub_eq_add_neg] at hx
    rcases supportSection_add_subset B S hS F U s (-t) hx with h | h
    · exact hs h
    · rw [supportSection_neg] at h
      exact ht h
  have hempty : supportSection B S hS F U (s - t) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx =>
      hx ((map_eq_zero_iff_le_zeroOpen B S hS F U (s - t) V e).1 hzero (hsub hx))
  exact sub_eq_zero.mp (eq_zero_of_supportSection_eq_empty B S hS F U (s - t) hempty)

end Determined

end AlgebraicGeometry.SmallEtale

end
